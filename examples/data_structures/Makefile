FSTAR_HOME=../..
include ../Makefile.include
all: uall

uall: BinaryTrees.uver bst RBTree.uver vector BinaryTreesEnumeration.uver MerkleTree.uver

bst: BinarySearchTree.uver BinarySearchTree0.uver BinarySearchTreeBasic.uver BinarySearchTreeFirst.uver

vector:
	$(FSTAR) --explicit_deps FStar.Pervasives.Native.fst FStar.Pervasives.fst ArrayRealized.fst Vector.fst
