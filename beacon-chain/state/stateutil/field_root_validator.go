package stateutil

import (
	"bytes"
	"encoding/binary"
	"math/bits"
	"runtime"
	"sync"

	"github.com/pkg/errors"
	fieldparams "github.com/prysmaticlabs/prysm/v5/config/fieldparams"
	"github.com/prysmaticlabs/prysm/v5/crypto/hash"
	"github.com/prysmaticlabs/prysm/v5/crypto/hash/htr"
	"github.com/prysmaticlabs/prysm/v5/encoding/ssz"

	ethpb "github.com/prysmaticlabs/prysm/v5/proto/prysm/v1alpha1"
	"github.com/sirupsen/logrus"
)

const (
	// number of field roots for the validator object.
	validatorFieldRoots = 8

	// Depth of tree representation of an individual
	// validator.
	// NumOfRoots = 2 ^ (TreeDepth)
	// 8 = 2 ^ 3
	validatorTreeDepth = 3
)

// ValidatorRegistryRoot computes the HashTreeRoot Merkleization of
// a list of validator structs according to the Ethereum
// Simple Serialize specification.
func ValidatorRegistryRoot(vals []*ethpb.Validator) ([32]byte, error) {
	return validatorRegistryRoot(vals)
}

func validatorRegistryRoot(validators []*ethpb.Validator) ([32]byte, error) {
	roots, err := OptimizedValidatorRoots(validators)
	if err != nil {
		return [32]byte{}, err
	}

	validatorsRootsRoot, err := ssz.BitwiseMerkleize(roots, uint64(len(roots)), fieldparams.ValidatorRegistryLimit)
	if err != nil {
		return [32]byte{}, errors.Wrap(err, "could not compute validator registry merkleization")
	}
	validatorsRootsBuf := new(bytes.Buffer)
	if err := binary.Write(validatorsRootsBuf, binary.LittleEndian, uint64(len(validators))); err != nil {
		return [32]byte{}, errors.Wrap(err, "could not marshal validator registry length")
	}
	// We need to mix in the length of the slice.
	var validatorsRootsBufRoot [32]byte
	copy(validatorsRootsBufRoot[:], validatorsRootsBuf.Bytes())
	res := ssz.MixInLength(validatorsRootsRoot, validatorsRootsBufRoot[:])

	return res, nil
}

func hashValidatorHelper(validators []*ethpb.Validator, roots [][32]byte, j int, groupSize int, wg *sync.WaitGroup) {
	defer wg.Done()
	for i := 0; i < groupSize; i++ {
		fRoots, err := ValidatorFieldRoots(validators[j*groupSize+i])
		if err != nil {
			logrus.WithError(err).Error("could not get validator field roots")
			return
		}
		for k, root := range fRoots {
			roots[(j*groupSize+i)*validatorFieldRoots+k] = root
		}
	}
}

// OptimizedValidatorRoots uses an optimized routine with gohashtree in order to
// derive a list of validator roots from a list of validator objects.
func OptimizedValidatorRoots(validators []*ethpb.Validator) ([][32]byte, error) {
	// Exit early if no validators are provided.
	if len(validators) == 0 {
		return [][32]byte{}, nil
	}
	wg := sync.WaitGroup{}
	n := runtime.GOMAXPROCS(0)
	rootsSize := len(validators) * validatorFieldRoots
	groupSize := len(validators) / n
	roots := make([][32]byte, rootsSize)
	wg.Add(n - 1)
	for j := 0; j < n-1; j++ {
		go hashValidatorHelper(validators, roots, j, groupSize, &wg)
	}
	for i := (n - 1) * groupSize; i < len(validators); i++ {
		fRoots, err := ValidatorFieldRoots(validators[i])
		if err != nil {
			return [][32]byte{}, errors.Wrap(err, "could not compute validators merkleization")
		}
		for k, root := range fRoots {
			roots[i*validatorFieldRoots+k] = root
		}
	}
	wg.Wait()

	// A validator's tree can represented with a depth of 3. As log2(8) = 3
	// Using this property we can lay out all the individual fields of a
	// validator and hash them in single level using our vectorized routine.
	for i := 0; i < validatorTreeDepth; i++ {
		// Overwrite input lists as we are hashing by level
		// and only need the highest level to proceed.
		roots = htr.VectorizedSha256(roots)
	}
	return roots, nil
}

// ValidatorRegistryProof computes the merkle proof for a validator at a specific index
// in the validator registry.
func ValidatorRegistryProof(validators []*ethpb.Validator, index uint64) ([][32]byte, error) {
	if index >= uint64(len(validators)) {
		return nil, errors.New("validator index out of bounds")
	}

	// First get all validator roots
	roots, err := OptimizedValidatorRoots(validators)
	if err != nil {
		return nil, errors.Wrap(err, "could not get validator roots")
	}

	depth := bits.Len64(uint64(len(validators) - 1)) // Calculate required depth

	// Generate proof
	proof := make([][32]byte, depth)
	tmp := roots
	for h := 0; h < depth; h++ {
		// Get the sibling index at height "h"
		idx := (index >> h) ^ 1
		if idx < uint64(len(tmp)) {
			proof[h] = tmp[idx]
		}

		// Move up one level in the tree
		newSize := (len(tmp) + 1) / 2
		newTmp := make([][32]byte, newSize)
		for i := 0; i < len(tmp)-1; i += 2 {
			concat := append(tmp[i][:], tmp[i+1][:]...)
			newTmp[i/2] = hash.Hash(concat)
		}
		// Handle odd number of elements
		if len(tmp)%2 == 1 {
			concat := append(tmp[len(tmp)-1][:], make([]byte, 32)...)
			newTmp[len(newTmp)-1] = hash.Hash(concat)
		}
		tmp = newTmp
	}

	return proof, nil
}

// VerifyValidatorProof verifies a merkle proof for a validator
func VerifyValidatorProof(validator *ethpb.Validator, index uint64, proof [][32]byte, root [32]byte) (bool, error) {
	// Get validator root
	validatorRoots, err := ValidatorFieldRoots(validator)
	if err != nil {
		return false, errors.Wrap(err, "could not get validator field roots")
	}

	// Hash up to get single validator root
	roots := validatorRoots
	for i := 0; i < validatorTreeDepth; i++ {
		roots = htr.VectorizedSha256(roots)
	}
	leaf := roots[0]

	// Verify the proof
	currentRoot := leaf
	for i, proofElement := range proof {
		position := (index >> uint(i)) & 1
		if position == 1 {
			concat := append(proofElement[:], currentRoot[:]...)
			currentRoot = hash.Hash(concat)
		} else {
			concat := append(currentRoot[:], proofElement[:]...)
			currentRoot = hash.Hash(concat)
		}
	}

	return bytes.Equal(currentRoot[:], root[:]), nil
}
