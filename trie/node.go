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

package trie

import (
	"fmt"
	"io"
	"math/big"
	"strings"

	"github.com/Onther-Tech/plasma-evm/common"
	"github.com/Onther-Tech/plasma-evm/crypto"
	"github.com/Onther-Tech/plasma-evm/rlp"
)

var indices = []string{"0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "a", "b", "c", "d", "e", "f", "[17]"}

type node interface {
	fstring(string) string
	cache() (hashNode, bool)
}

type (
	branchNode struct {
		Children [3]node
		flags    nodeFlag
	}
	hashNode  []byte
	valueNode struct {
		Value     []byte
		keylength uint32
		Hash      common.Hash
	}
	singleNode []byte
)

// nilValueNode is used when collapsing internal trie nodes for hashing, since
// unset children need to serialize correctly.
var nilValueNode = valueNode{nil, 0, common.Hash{}}

// EncodeRLP encodes a full node into the consensus RLP format.
func (n *branchNode) EncodeRLP(w io.Writer) error {
	var nodes [3]hashNode

	for i := 0; i < 3; i++ {
		child := n.Children[i]
		if child != nil {
			switch tn := child.(type) {
			case *branchNode:
				nodes[i] = tn.flags.hash
			case hashNode:
				nodes[i] = tn
			case valueNode:
				nodes[i] = tn.Hash[:]
			}
		} else {
			nodes[i] = nil
		}
	}
	return rlp.Encode(w, nodes)
}

func (n valueNode) EncodeRLP(w io.Writer) error {
	return rlp.Encode(w, []interface{}{n.Value, n.keylength})
}

func (n *branchNode) copy() *branchNode { copy := *n; return &copy }

// nodeFlag contains caching-related metadata about a node.
type nodeFlag struct {
	hash  hashNode // cached hash of the node (may be nil)
	dirty bool     // whether the node has changes that must be written to the database
}

func (n *branchNode) cache() (hashNode, bool) { return n.flags.hash, n.flags.dirty }
func (n hashNode) cache() (hashNode, bool)    { return nil, true }
func (n valueNode) cache() (hashNode, bool)   { return nil, true }
func (n singleNode) cache() (hashNode, bool)  { return nil, true }

// Pretty printing.
func (n *branchNode) String() string { return n.fstring("") }
func (n hashNode) String() string    { return n.fstring("") }
func (n valueNode) String() string   { return n.fstring("") }
func (n singleNode) String() string  { return n.fstring("") }

func (n *branchNode) fstring(ind string) string {
	resp := fmt.Sprintf("[\n%s  ", ind)
	for i, node := range &n.Children {
		if node == nil {
			resp += fmt.Sprintf("%s: <nil> ", indices[i])
		} else {
			resp += fmt.Sprintf("%s: %v", indices[i], node.fstring(ind+"  "))
		}
	}
	return resp + fmt.Sprintf("\n%s] ", ind)
}
func (n hashNode) fstring(ind string) string {
	return fmt.Sprintf("<%x> ", []byte(n))
}
func (n valueNode) fstring(ind string) string {
	return fmt.Sprintf("%x ", []byte(n.Value))
}

func (n singleNode) fstring(ind string) string {
	return fmt.Sprintf("%x ", []byte(n))
}

func mustDecodeNode(hash, buf []byte, depth uint32) node {
	n, err := decodeNode(hash, buf)
	if err != nil {
		if len(buf) > 32 {
			var decoded []byte
			if err := rlp.DecodeBytes(buf, &decoded); err == nil {
				return singleNode(decoded)
			} else {
			}
		}
		panic(fmt.Sprintf("node %x: %v", hash, err))
	}
	return n
}

// decodeNode parses the RLP encoding of a trie node.
func decodeNode(hash, buf []byte) (node, error) {
	if len(buf) == 0 {
		return nil, io.ErrUnexpectedEOF
	}
	elems, _, err := rlp.SplitList(buf)
	if err != nil {
		return nil, fmt.Errorf("decode error: %v", err)
	}
	switch c, _ := rlp.CountValues(elems); c {
	case 1:
		var n hashNode
		if err := rlp.DecodeBytes(elems, &n); err != nil {
			return nil, err
		}
		return n, nil
	case 2:
		n, err := decodeValue(elems)
		return n, wrapError(err, "value")
	case 3:
		n, err := decodeBranch(hash, elems)
		return n, wrapError(err, "branch")
	default:
		return nil, fmt.Errorf("invalid number of list elements: %v", c)
	}
}

func decodeValue(elems []byte) (node, error) {
	n := valueNode{}
	_, val, rest, err := rlp.Split(elems)
	if err != nil {
		return nil, err
	}
	_, val, rest, err = rlp.Split(rest)
	if err := rlp.DecodeBytes(val, &n.keylength); err != nil {
		return nil, err
	}
	n.Hash = crypto.Keccak256Hash(n.Value)
	return n, nil
}

func decodeBranch(hash, elems []byte) (node, error) {
	n := &branchNode{flags: nodeFlag{hash: hash}}

	for i := 0; i < 3; i++ {
		cld, rest, err := decodeRef(elems)
		if err != nil {
			return n, wrapError(err, fmt.Sprintf("[%d]", i))
		}
		n.Children[i], elems = cld, rest
	}
	return n, nil
}

const hashLen = len(common.Hash{})

func decodeRef(buf []byte) (node, []byte, error) {
	kind, val, rest, err := rlp.Split(buf)
	if err != nil {
		return nil, buf, err
	}
	switch {
	case kind == rlp.List:
		if val == nil || len(val) == 0 {
			return nil, rest, nil
		}
		// 'embedded' node reference. The encoding must be smaller
		// than a hash in order to be valid.
		n, err := decodeNode(nil, buf)
		return n, rest, err
	case kind == rlp.String && len(val) == 0:
		// empty node
		return nil, rest, nil
	case kind == rlp.String && len(val) == 32:
		return append(hashNode{}, val...), rest, nil
	case kind == rlp.String && len(val) > 32:
		return append(singleNode{}, val...), rest, nil
	default:
		return nil, nil, fmt.Errorf("invalid RLP string size %d (want 0 or 32)", len(val))
	}
}

// wraps a decoding error with information about the path to the
// invalid child node (for debugging encoding issues).
type decodeError struct {
	what  error
	stack []string
}

func wrapError(err error, ctx string) error {
	if err == nil {
		return nil
	}
	if decErr, ok := err.(*decodeError); ok {
		decErr.stack = append(decErr.stack, ctx)
		return decErr
	}
	return &decodeError{err, []string{ctx}}
}

func (err *decodeError) Error() string {
	return fmt.Sprintf("%v (decode path: %s)", err.what, strings.Join(err.stack, "<-"))
}

type singleNodeInfo struct {
	depth  uint32
	path   *big.Int
	keylen uint32
	value  []byte
}

func (n *singleNodeInfo) EncodeRLP(w io.Writer) error {
	return rlp.Encode(w, []interface{}{n.depth, n.path.Bytes(), n.keylen, n.value})
}

func (e *singleNodeInfo) DecodeRLP(s *rlp.Stream) error {
	var entry struct {
		depth  uint32
		path   []byte
		keylen uint32
		value  []byte
	}

	s.List()

	buf, _ := s.Uint()
	entry.depth = uint32(buf)
	buf2, _ := s.Bytes()
	entry.path = buf2
	buf, _ = s.Uint()
	entry.keylen = uint32(buf)
	buf2, _ = s.Bytes()
	entry.value = buf2

	e.depth = entry.depth
	e.path = new(big.Int).SetBytes(entry.path)
	e.keylen = entry.keylen
	e.value = entry.value
	return nil
}

func encodeSingleKeyNode(depth uint32, path *big.Int, value valueNode) singleNode {
	n := &singleNodeInfo{depth: depth, path: path, keylen: value.keylength, value: value.Value}
	r, err := rlp.EncodeToBytes(n)
	if err != nil {
	}
	return r
}

func decodeSingleKeyNode(n singleNode) (uint32, *big.Int, valueNode) {
	var nn singleNodeInfo
	rlp.DecodeBytes(n, &nn)
	return nn.depth, nn.path, valueNode{nn.value, nn.keylen, crypto.Keccak256Hash(nn.value)}
}
