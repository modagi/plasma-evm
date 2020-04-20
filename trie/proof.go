// Copyright 2015 The go-ethereum Authors
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

package trie

import (
	"bytes"
	"fmt"
	"math/big"

	"github.com/Onther-Tech/plasma-evm/common"
	"github.com/Onther-Tech/plasma-evm/crypto"
	"github.com/Onther-Tech/plasma-evm/ethdb"
	"github.com/Onther-Tech/plasma-evm/log"
	"github.com/Onther-Tech/plasma-evm/rlp"
)

// Prove constructs a merkle proof for key. The result contains all encoded nodes
// on the path to the value at key. The value itself is also included in the last
// node and can be retrieved by verifying the proof.
//
// If the trie does not contain a value for key, the returned proof contains all
// nodes of the longest existing prefix of the key (at least the root node), ending
// with the node that proves the absence of the key.
func (t *Trie) Prove(key []byte, fromLevel uint, proofDb ethdb.KeyValueWriter) error {
	// Collect all nodes on the path to key.
	tn := t.root
	path := KeyToPath(key)
	var sidenodes []common.Hash

	for i := 0; i < 256; {
		switch n := tn.(type) {
		case *branchNode:
			branch := new(big.Int).And(new(big.Int).Set(new(big.Int).Rsh(path, 255)), big.NewInt(1)).Uint64()
			switch tn := n.Children[1-branch].(type) {
			case *branchNode:
				sidenodes = append(sidenodes, common.BytesToHash(tn.flags.hash))
			case hashNode:
				sidenodes = append(sidenodes, common.BytesToHash(tn))
			case nil:
				sidenodes = append(sidenodes, common.BytesToHash(zerohashes[i+1][:]))
			case valueNode:
				sidenodes = append(sidenodes, tn.Hash)
			default:
			}
			tn = n.Children[branch]
			path.Lsh(path, 1)
			i++
		case hashNode:
			var err error
			tn, err = t.resolveHash(n, 0)
			if err != nil {
				log.Error(fmt.Sprintf("Unhandled trie error: %v", err))
				return err
			}
		case nil:
			sidenodes = append(sidenodes, common.BytesToHash(zerohashes[i+1][:]))
			i++
		default:
			panic(fmt.Sprintf("%T: invalid node: %v", tn, tn))
		}
	}
	cp := CompressProof(sidenodes)
	proofDb.Put(t.root.(*branchNode).flags.hash, cp)
	if v, ok := tn.(valueNode); ok {
		proofDb.Put(key, v.Value)
	} else {
	}
	return nil
}

func CompressProof(nodes []common.Hash) []byte {
	MakeZeroHashes()
	buf := make([][]byte, 0, 257)
	buf = append(buf, bytes.Repeat([]byte{0x00}, 32))
	for i, p := range nodes {
		if bytes.Equal(p[:], zerohashes[i+1][:]) {
			buf[0][uint(i/8)] ^= (1 << (i % 8))
		} else {
			buf = append(buf, buf[len(buf)-1])
			copy(buf[2:], buf[1:len(buf)-1])
			enc, _ := rlp.EncodeToBytes(p)
			buf[1] = enc
		}
	}
	enc, _ := rlp.EncodeToBytes(buf)
	return enc
}

// Prove constructs a merkle proof for key. The result contains all encoded nodes
// on the path to the value at key. The value itself is also included in the last
// node and can be retrieved by verifying the proof.
//
// If the trie does not contain a value for key, the returned proof contains all
// nodes of the longest existing prefix of the key (at least the root node), ending
// with the node that proves the absence of the key.
func (t *SecureTrie) Prove(key []byte, fromLevel uint, proofDb ethdb.KeyValueWriter) error {
	return t.trie.Prove(key, fromLevel, proofDb)
}

// VerifyProof checks merkle proofs. The given proof must contain the value for
// key in a trie with the given root hash. VerifyProof returns an error if the
// proof contains invalid trie nodes or the wrong value.
func VerifyProof(rootHash common.Hash, key []byte, proofDb ethdb.KeyValueReader) (value []byte, nodes int, err error) {
	path := KeyToPath(key)
	enc, _ := proofDb.Get(rootHash[:])
	if enc == nil {
		return nil, 0, fmt.Errorf("proof root (hash %064x) missing", rootHash)
	}
	value, err = proofDb.Get(key)
	if err != nil {
		value = nil
	}
	buf := enc
	_, val, rest, err := rlp.Split(buf)
	if err != nil {
		return nil, 0, err
	}
	bits, rest, err := rlp.SplitString(val)
	if err != nil {
		// TODO: error
		return nil, 0, &MissingNodeError{rootHash, 0}
	}
	buf = rest
	var hashed hashNode
	valuehash := crypto.Keccak256Hash(value)
	for i := 0; i < 256; i++ {
		var side hashNode
		if bits[uint((255-i)/8)]&(1<<((255-i)%8)) != 0 {
			side = zerohashes[256-i]
		} else {
			val, rest, err := rlp.SplitString(buf)
			if err != nil {
				break
			}
			side, _, _ = rlp.SplitString(val)
			buf = rest
		}

		index := new(big.Int).And(new(big.Int).Set(path), big.NewInt(1)).Uint64()
		b := branchNode{}
		b.Children[index] = hashNode(valuehash[:])
		b.Children[1-index] = hashNode(side[:])
		hashed = hashBranchNode(&b, uint32(i))
		valuehash.SetBytes(hashed[:])
		path.Rsh(path, 1)
	}

	if rootHash != common.BytesToHash(hashed) {
		return nil, 0, fmt.Errorf("proof failed, got 0x%x want 0x%x", hashed[:], rootHash)
	}
	return value, 256, nil
}

func get(tn node, path *big.Int) (*big.Int, node) {
	for {
		switch n := tn.(type) {
		case *branchNode:
			branch := new(big.Int).And(new(big.Int).Set(new(big.Int).Rsh(path, 255)), big.NewInt(1)).Uint64()
			tn = n.Children[branch]
			path.Lsh(path, 1)
		case hashNode:
			return path, n
		case nil:
			return path, nil
		case valueNode:
			return nil, n
		default:
			panic(fmt.Sprintf("%T: invalid node: %v", tn, tn))
		}
	}
}
