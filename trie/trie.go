// Copyright 2014 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// The go-ethereum library is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// The go-ethereum library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with the go-ethereum library. If not, see <http://www.gnu.org/licenses/>.

// Package trie implements Merkle Patricia Tries.
package trie

import (
	"bytes"
	"fmt"
	"math/big"

	"github.com/Onther-Tech/plasma-evm/common"
	"github.com/Onther-Tech/plasma-evm/crypto"
	"github.com/Onther-Tech/plasma-evm/log"
	"github.com/Onther-Tech/plasma-evm/rlp"
)

var (
	// emptyRoot is the known root hash of an empty trie.
	emptyRoot = common.HexToHash("1b4fa5f485ec023075da4ff667506f4a067235f6019e49a8f72e3ce96519d83a")

	// emptyState is the known hash of an empty state trie entry.
	emptyState = crypto.Keccak256Hash(nil)
)

// LeafCallback is a callback type invoked when a trie operation reaches a leaf
// node. It's used by state sync and commit to allow handling external references
// between account and storage tries.
type LeafCallback func(leaf []byte, parent common.Hash) error

// Trie is a Merkle Patricia Trie.
// The zero value is an empty trie with no database.
// Use New to create a trie that sits on top of a database.
//
// Trie is not safe for concurrent use.
type Trie struct {
	db   *Database
	root node
}

// newFlag returns the cache flag value for a newly created node.
func (t *Trie) newFlag() nodeFlag {
	return nodeFlag{dirty: true}
}

// New creates a trie with an existing root node from db.
//
// If root is the zero hash or the sha3 hash of an empty string, the
// trie is initially empty and does not require a database. Otherwise,
// New will panic if db is nil and returns a MissingNodeError if root does
// not exist in the database. Accessing the trie loads nodes from db on demand.
func New(root common.Hash, db *Database) (*Trie, error) {
	if db == nil {
		panic("trie.New called without a database")
	}
	tt256m1 = new(big.Int).Sub(new(big.Int).Exp(big.NewInt(2), big.NewInt(256), nil), big.NewInt(1))
	trie := &Trie{db: db}
	if root != (common.Hash{}) && root != emptyRoot {
		rootnode, err := trie.resolveHash(root[:], 0)
		if err != nil {
			return nil, err
		}
		trie.root = rootnode
	}
	return trie, nil
}

// NodeIterator returns an iterator that returns nodes of the trie. Iteration starts at
// the key after the given start key.
func (t *Trie) NodeIterator(start []byte) NodeIterator {
	return newNodeIterator(t, start)
}

// Get returns the value for key stored in the trie.
// The value bytes must not be modified by the caller.
func (t *Trie) Get(key []byte) []byte {
	res, err := t.TryGet(key)
	if err != nil {
		log.Error(fmt.Sprintf("Unhandled trie error: %v", err))
	}
	return res
}

// TryGet returns the value for key stored in the trie.
// The value bytes must not be modified by the caller.
// If a node was not found in the database, a MissingNodeError is returned.
func (t *Trie) TryGet(key []byte) ([]byte, error) {
	if len(key) > 32 {
		key = crypto.Keccak256(key)
	}
	path := KeyToPath(key)
	value, newroot, didResolve, err := t.tryGet(t.root, 0, path)
	if err == nil && didResolve {
		t.root = newroot
	}
	return value, err
}

func KeyToPath(key []byte) (result *big.Int) {
	result = big.NewInt(0)
	for _, c := range key[:] {
		result.Add(result.Lsh(result, 8), big.NewInt(int64(c)))
	}
	return result
}

func PathToKey(path *big.Int, keylen uint32) []byte {
	tmp1 := new(big.Int).Set(path)
	tmp2 := new(big.Int).And(tmp1, tt256m1)
	tmp := tmp2.Bytes()
	if len(tmp) != 32 {
		for len(tmp) < 32 {
			tmp = append([]byte("\x00"), tmp...)
		}
	}
	return tmp[32-keylen:]
}

func (t *Trie) tryGet(origNode node, depth uint32, path *big.Int) (value []byte, newnode node, didResolve bool, err error) {
	switch n := (origNode).(type) {
	case nil:
		return nil, nil, false, nil
	case singleNode:
		return n[:], n, false, nil
	case valueNode:
		return n.Value, n, false, nil
	case *branchNode:
		hashed, _ := n.cache()
		if bytes.Equal(hashed, zerohashes[depth][:]) {
			return nil, n, false, nil
		} else if ok, _ := t.getSingleKeySubtree(n, depth); ok {
			_, path2, value := decodeSingleKeyNode(n.Children[2].(singleNode))
			if path.Cmp(path2) == 0 {
				return value.Value, n, false, nil
			} else {
				return nil, n, false, nil
			}
		} else {
			if new(big.Int).And(new(big.Int).Rsh(path, 255), big.NewInt(1)).Uint64() == 1 {
				value, _, _, err := t.tryGet(n.Children[1], depth+1, new(big.Int).Lsh(path, 1))
				if err != nil {
					//TODO: error
				}
				return value, n, false, nil
			} else {
				value, _, _, err := t.tryGet(n.Children[0], depth+1, new(big.Int).Lsh(path, 1))
				if err != nil {
					//TODO: error
				}
				return value, n, false, nil
			}
		}
	case hashNode:
		if bytes.Equal(n, zerohashes[depth][:]) {
			return nil, n, false, nil
		}
		child, err := t.resolveHash(n, depth)
		if err != nil {
			return nil, n, true, err
		}
		value, newnode, _, err := t.tryGet(child, depth, path)
		return value, newnode, true, err
	default:
		panic(fmt.Sprintf("%T: invalid node: %v", origNode, origNode))
	}
}

// Update associates key with value in the trie. Subsequent calls to
// Get will return value. If value has length zero, any existing value
// is deleted from the trie and calls to Get will return nil.
//
// The value bytes must not be modified by the caller while they are
// stored in the trie.
func (t *Trie) Update(key, value []byte) {
	if err := t.TryUpdate(key, value); err != nil {
		log.Error(fmt.Sprintf("Unhandled trie error: %v", err))
	}
}

// TryUpdate associates key with value in the trie. Subsequent calls to
// Get will return value. If value has length zero, any existing value
// is deleted from the trie and calls to Get will return nil.
//
// The value bytes must not be modified by the caller while they are
// stored in the trie.
//
// If a node was not found in the database, a MissingNodeError is returned.
func (t *Trie) TryUpdate(key, value []byte) error {
	if len(key) > 32 {
		key = crypto.Keccak256(key)
	}
	path := KeyToPath(key)
	if len(value) != 0 {
		_, n, err := t.insert(t.root, 0, key, path, valueNode{value, uint32(len(key)), crypto.Keccak256Hash(value)})
		if err != nil {
			return err
		}
		t.root = n
	} else {
		_, n, err := t.delete(t.root, 0, nil, path)
		if err != nil {
			return err
		}
		t.root = n
	}
	return nil
}

func hashBranchNode(n *branchNode, depth uint32) hashNode {
	h := newHasher(nil)
	defer returnHasherToPool(h)
	var buf []byte
	for i := 0; i < 2; i++ {
		var cn []byte
		switch n := n.Children[i].(type) {
		case *branchNode:
			cn = n.flags.hash
		case hashNode:
			cn = n
		case valueNode:
			cn = n.Hash[:]
		case nil:
			cn = zerohashes[depth+1][:]
		default:
			// TODO: error
		}
		en, err := rlp.EncodeToBytes(cn)
		if err != nil {
			// TODO: error
		}
		buf = append(buf, en...)
	}

	tmp := h.makeHashNode(buf)
	return tmp
}

func (t *Trie) makeSingleKeyNode(n node, path *big.Int, depth uint32, value valueNode) node {
	if depth == 256 {
		return valueNode(value)
	}
	var bn *branchNode
	switch n := n.(type) {
	case hashNode:
		if n == nil || len(n) == 0 {
			bn = &branchNode{flags: t.newFlag()}
		} else {
			nn, err := t.getFromHashNode(n, depth)
			if err != nil {
				// TODO: error
			}
			bn = nn.(*branchNode)
		}
	case *branchNode:
		bn = n
	}
	h := newHasher(nil)
	defer returnHasherToPool(h)
	if new(big.Int).And(new(big.Int).Rsh(path, 255), big.NewInt(1)).Uint64() == 1 {
		if bn.Children[1] == nil {
			cn := &branchNode{flags: t.newFlag()}
			cn.flags.hash = zerohashes[depth+1][:]
			bn.Children[1] = cn
		}
		nn := t.makeSingleKeyNode(bn.Children[1], new(big.Int).Set(path).Lsh(path, 1), depth+1, value)
		bn.Children[1] = nn
		bn.flags.hash = hashBranchNode(bn, depth)
		bn.flags.dirty = true
		return bn
	} else {
		if bn.Children[0] == nil {
			cn := &branchNode{flags: t.newFlag()}
			cn.flags.hash = zerohashes[depth+1][:]
			bn.Children[0] = cn
		}
		nn := t.makeSingleKeyNode(bn.Children[0], new(big.Int).Set(path).Lsh(path, 1), depth+1, value)
		bn.Children[0] = nn
		bn.flags.hash = hashBranchNode(bn, depth)
		bn.flags.dirty = true
		return bn
	}
}

func (t *Trie) makeDoubleKeyNode(n node, path1, path2 *big.Int, depth uint32, value1, value2 valueNode) node {
	if depth == 256 {
		//TODO: error
		return nil
	}
	var bn *branchNode
	switch n := n.(type) {
	case hashNode:
		nn, err := t.getFromHashNode(n, depth)
		if err != nil {
			// TODO: error
		}
		bn = nn.(*branchNode)
	case *branchNode:
		bn = n
	}
	var cn node
	h := newHasher(nil)
	defer returnHasherToPool(h)
	if new(big.Int).And(new(big.Int).Rsh(path1, 255), big.NewInt(1)).Uint64() == 1 {
		if new(big.Int).And(new(big.Int).Rsh(path2, 255), big.NewInt(1)).Uint64() == 1 {
			if bn.Children[1] == nil {
				bn.Children[1] = &branchNode{flags: t.newFlag()}
			}
			tmp := t.makeDoubleKeyNode(bn.Children[1], new(big.Int).Lsh(path1, 1), new(big.Int).Lsh(path2, 1), depth+1, value1, value2)
			bn.Children[1] = tmp
			bn.flags.hash = hashBranchNode(bn, depth)
			bn.flags.dirty = true
			return bn
		} else {
			for i := 0; i < 2; i++ {
				if bn.Children[i] == nil {
					bn.Children[i] = &branchNode{flags: t.newFlag()}
				}
			}
			L := t.makeSingleKeyNode(bn.Children[0], new(big.Int).Lsh(path2, 1), depth+1, value2)
			R := t.makeSingleKeyNode(bn.Children[1], new(big.Int).Lsh(path1, 1), depth+1, value1)
			if v, ok := L.(*branchNode); ok {
				v.Children[2] = encodeSingleKeyNode(depth+1, new(big.Int).Lsh(path2, 1), value2)
			}
			if v, ok := R.(*branchNode); ok {
				v.Children[2] = encodeSingleKeyNode(depth+1, new(big.Int).Lsh(path1, 1), value1)
			}
			bn.Children[0] = L
			bn.Children[1] = R
			bn.flags.hash = hashBranchNode(bn, depth)
			bn.flags.dirty = true
			cn = bn
		}
	} else {
		if new(big.Int).And(new(big.Int).Rsh(path2, 255), big.NewInt(1)).Uint64() == 1 {
			for i := 0; i < 2; i++ {
				if bn.Children[i] == nil {
					bn.Children[i] = &branchNode{flags: t.newFlag()}
				}
			}
			L := t.makeSingleKeyNode(bn.Children[0], new(big.Int).Lsh(path1, 1), depth+1, value1)
			R := t.makeSingleKeyNode(bn.Children[1], new(big.Int).Lsh(path2, 1), depth+1, value2)
			if v, ok := L.(*branchNode); ok {
				v.Children[2] = encodeSingleKeyNode(depth+1, new(big.Int).Lsh(path1, 1), value1)
			}
			if v, ok := R.(*branchNode); ok {
				v.Children[2] = encodeSingleKeyNode(depth+1, new(big.Int).Lsh(path2, 1), value2)
			}
			bn.Children[0] = L
			bn.Children[1] = R
			bn.flags.hash = hashBranchNode(bn, depth)
			bn.flags.dirty = true
			cn = bn
		} else {
			if bn.Children[0] == nil {
				bn.Children[0] = &branchNode{flags: t.newFlag()}
			}
			tmp := t.makeDoubleKeyNode(bn.Children[0], new(big.Int).Lsh(path1, 1), new(big.Int).Lsh(path2, 1), depth+1, value1, value2)
			bn.Children[0] = tmp
			bn.flags.hash = hashBranchNode(bn, depth)
			bn.flags.dirty = true
			cn = bn
		}
	}

	return cn
}

func (t *Trie) getSingleKeySubtree(n *branchNode, depth uint32) (bool, node) {
	var singlenode singleNode
	switch cn := n.Children[2].(type) {
	case hashNode:
		copy(singlenode[:], cn[:])
	case singleNode:
		singlenode = cn
	}
	var sn node
	if singlenode != nil && len(singlenode) > 0 {
		return true, nil
	}
	//TODO: remove node
	return sn != nil, sn
}

func (t *Trie) getFromHashNode(n node, depth uint32) (node, error) {
	var hn hashNode
	switch n := n.(type) {
	case hashNode:
		hn = n
	}

	switch v := n.(type) {
	case *branchNode:
		if bytes.Equal(v.flags.hash, zerohashes[depth][:]) {
			newNode := &branchNode{flags: t.newFlag()}
			return newNode, nil
		}
	case hashNode:
		if bytes.Equal(v[:], zerohashes[depth][:]) {
			newNode := &branchNode{flags: t.newFlag()}
			return newNode, nil
		}
	}

	// We've hit a part of the trie that isn't loaded yet. Load
	// the node and insert into it. This leaves all child nodes on
	// the path to the value in the trie.
	rn, err := t.resolveHash(hn, depth)
	if err != nil {
		return nil, err
	}
	return rn, nil
}

func (t *Trie) insert(n node, depth uint32, key []byte, path *big.Int, value node) (bool, node, error) {
	if depth == 256 {
		if v, ok := n.(valueNode); ok {
			return !bytes.Equal(v.Value, value.(valueNode).Value), value, nil
		}
		return true, value, nil
	}
	switch n := n.(type) {
	case *branchNode:
		newpath := new(big.Int).Set(path)
		if bytes.Equal(n.flags.hash, zerohashes[depth][:]) {
			nn := t.makeSingleKeyNode(n, newpath, depth, value.(valueNode))
			nn.(*branchNode).Children[2] = encodeSingleKeyNode(depth, newpath, value.(valueNode))
			nn.(*branchNode).flags.hash = hashBranchNode(nn.(*branchNode), depth)
			nn.(*branchNode).flags.dirty = true
			return true, nn, nil
		} else if ok, _ := t.getSingleKeySubtree(n, depth); ok {
			_, path2, value2 := decodeSingleKeyNode(n.Children[2].(singleNode))
			if newpath.Cmp(path2) == 0 {
				n.Children[2] = nil
				nn := t.makeSingleKeyNode(n, newpath, depth, value.(valueNode))
				nn.(*branchNode).Children[2] = encodeSingleKeyNode(depth, newpath, value.(valueNode))
				nn.(*branchNode).flags.hash = hashBranchNode(nn.(*branchNode), depth)
				nn.(*branchNode).flags.dirty = true
				return true, nn, nil
			} else {
				n.Children[2] = nil
				nn := t.makeDoubleKeyNode(n, newpath, path2, depth, value.(valueNode), value2)
				nn.(*branchNode).flags.hash = hashBranchNode(nn.(*branchNode), depth)
				nn.(*branchNode).flags.dirty = true
				return true, nn, nil
			}
		}
		index := new(big.Int).And(new(big.Int).Rsh(newpath, 255), big.NewInt(1)).Uint64()
		ok, nn, err := t.insert(n.Children[index], depth+1, key, new(big.Int).Lsh(newpath, 1), value)
		if !ok || err != nil {
			//TODO: error
		}

		n.Children[index] = nn
		n.flags.hash = hashBranchNode(n, depth)
		n.flags.dirty = true
		return true, n, nil
	case nil:
		MakeZeroHashes()
		newNode := &branchNode{flags: t.newFlag()}
		nn := t.makeSingleKeyNode(newNode, path, depth, value.(valueNode))
		nn.(*branchNode).Children[2] = encodeSingleKeyNode(depth, path, value.(valueNode))
		nn.(*branchNode).flags.hash = hashBranchNode(nn.(*branchNode), depth)
		nn.(*branchNode).flags.dirty = true
		return true, nn, nil
	case hashNode:
		rn, err := t.getFromHashNode(n, depth)
		if err != nil {
			return false, rn, err
		}
		dirty, nn, err := t.insert(rn, depth, key, path, value)
		if !dirty || err != nil {
			return false, rn, err
		}
		return true, nn, nil

	default:
		panic(fmt.Sprintf("%T: invalid node: %v", n, n))
	}
}

// Delete removes any existing value for key from the trie.
func (t *Trie) Delete(key []byte) {
	if err := t.TryDelete(key); err != nil {
		log.Error(fmt.Sprintf("Unhandled trie error: %v", err))
	}
}

// TryDelete removes any existing value for key from the trie.
// If a node was not found in the database, a MissingNodeError is returned.
func (t *Trie) TryDelete(key []byte) error {
	if len(key) > 32 {
		key = crypto.Keccak256(key)
	}
	path := KeyToPath(key)
	_, n, err := t.delete(t.root, 0, key, path)
	if err != nil {
		return err
	}
	t.root = n
	return nil
}

// delete returns the new root of the trie with key deleted.
// It reduces the trie to minimal form by simplifying
// nodes on the way up after deleting recursively.
func (t *Trie) delete(n node, depth uint32, key []byte, path *big.Int) (bool, node, error) {
	switch n := n.(type) {
	case *branchNode:
		branch := new(big.Int).And(new(big.Int).Rsh(path, 255), big.NewInt(1)).Uint64()
		dirty, nn, err := t.delete(n.Children[branch], depth+1, key, path.Lsh(path, 1))
		n.Children[branch] = nn
		if !dirty || err != nil {
			return false, n, err
		}
		n = n.copy()
		n.flags = t.newFlag()
		n.flags.hash = hashBranchNode(n, depth)
		n.flags.dirty = true

		return true, n, nil

	case valueNode:
		return true, nil, nil

	case nil:
		return false, nil, nil

	case hashNode:
		// We've hit a part of the trie that isn't loaded yet. Load
		// the node and delete from it. This leaves all child nodes on
		// the path to the value in the trie.
		rn, err := t.resolveHash(n, depth)
		if err != nil {
			return false, nil, err
		}
		if depth == 256 {
			return true, nil, nil
		}
		dirty, nn, err := t.delete(rn, depth, key, path)
		if !dirty || err != nil {
			return false, rn, err
		}
		return true, nn, nil

	default:
		panic(fmt.Sprintf("%T: invalid node: %v (%v)", n, n, key))
	}
}

func concat(s1 []byte, s2 ...byte) []byte {
	r := make([]byte, len(s1)+len(s2))
	copy(r, s1)
	copy(r[len(s1):], s2)
	return r
}

func (t *Trie) resolve(n node, prefix []byte) (node, error) {
	if n, ok := n.(hashNode); ok {
		return t.resolveHash(n, 0)
	}
	return n, nil
}

func (t *Trie) resolveHash(n hashNode, depth uint32) (node, error) {
	hash := common.BytesToHash(n)
	if node := t.db.node(hash, depth); node != nil {
		return node, nil
	}
	return nil, &MissingNodeError{NodeHash: hash, Depth: depth}
}

// Hash returns the root hash of the trie. It does not write to the
// database and can be used even if the trie doesn't have one.
func (t *Trie) Hash() common.Hash {
	hash, cached, _ := t.hashRoot(nil, nil)
	t.root = cached
	return common.BytesToHash(hash.(hashNode))
}

// Commit writes all nodes to the trie's memory database, tracking the internal
// and external (for account tries) references.
func (t *Trie) Commit(onleaf LeafCallback) (root common.Hash, err error) {
	if t.db == nil {
		panic("commit called on trie with nil database")
	}
	hash, cached, err := t.hashRoot(t.db, onleaf)
	if err != nil {
		return common.Hash{}, err
	}
	t.root = cached
	return common.BytesToHash(hash.(hashNode)), nil
}

func (t *Trie) hashRoot(db *Database, onleaf LeafCallback) (node, node, error) {
	if t.root == nil {
		return hashNode(emptyRoot[:]), nil, nil
	}
	h := newHasher(onleaf)
	defer returnHasherToPool(h)
	return h.hash(t.root, db, true)
}
