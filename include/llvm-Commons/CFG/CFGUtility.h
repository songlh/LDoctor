

#ifndef _H_SONGLH_CFGUTILITY
#define _H_SONGLH_CFGUTILITY



#include "llvm/IR/Function.h"
#include "llvm/ADT/DepthFirstIterator.h"
#include "llvm/ADT/GraphTraits.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/Support/DOTGraphTraits.h"

#include <map>
#include <set>
#include <iterator>

class ControlDependenceGraph;
class ControlDependenceNode;

class ControlDependenceNode 
{
	public:
	enum EdgeType { TRUE, FALSE, OTHER };
	typedef std::set<ControlDependenceNode *>::iterator       node_iterator;
	typedef std::set<ControlDependenceNode *>::const_iterator const_node_iterator;

	struct edge_iterator 
	{
		typedef node_iterator::value_type      value_type;
		typedef node_iterator::difference_type difference_type;
		typedef node_iterator::reference       reference;
		typedef node_iterator::pointer         pointer;
		typedef std::input_iterator_tag        iterator_category;

		edge_iterator(ControlDependenceNode *n) : 
			node(n), stage(TRUE), it(n->TrueChildren.begin()), end(n->TrueChildren.end()) 
		{
			while ((stage != OTHER) && (it == end)) this->operator++();
		}
    
		edge_iterator(ControlDependenceNode *n, EdgeType t, node_iterator i, node_iterator e) :
			node(n), stage(t), it(i), end(e) 
		{
			while ((stage != OTHER) && (it == end)) this->operator++();
		}
		EdgeType type() const { return stage; }
		bool operator==(edge_iterator const &other) const 
		{ 
			return (this->stage == other.stage) && (this->it == other.it);
		}
		bool operator!=(edge_iterator const &other) const { return !(*this == other); }
		reference operator*()  { return *this->it; }
		pointer   operator->() { return &*this->it; }
		edge_iterator& operator++() 
		{
			if (it != end) ++it;
			while ((stage != OTHER) && (it == end)) 
			{
				if (stage == TRUE) {
				it = node->FalseChildren.begin();
				end = node->FalseChildren.end();
				stage = FALSE;
				} 
				else 
				{
					it = node->OtherChildren.begin();
					end = node->OtherChildren.end();
					stage = OTHER;
				}
			}
			return *this;
		}
		edge_iterator operator++(int) 
		{
			edge_iterator ret(*this);
			assert(ret.stage == OTHER || ret.it != ret.end);
			this->operator++();
			return ret;
		}
	private:
		ControlDependenceNode *node;
		EdgeType stage;
		node_iterator it, end;
	};

	edge_iterator begin() { return edge_iterator(this); }
	edge_iterator end()   { return edge_iterator(this, OTHER, OtherChildren.end(), OtherChildren.end()); }

	node_iterator true_begin()   { return TrueChildren.begin(); }
	node_iterator true_end()     { return TrueChildren.end(); }

	node_iterator false_begin()  { return FalseChildren.begin(); }
	node_iterator false_end()    { return FalseChildren.end(); }

	node_iterator other_begin()  { return OtherChildren.begin(); }
	node_iterator other_end()    { return OtherChildren.end(); }

	node_iterator parent_begin() { return Parents.begin(); }
	node_iterator parent_end()   { return Parents.end(); }
	const_node_iterator parent_begin() const { return Parents.begin(); }
	const_node_iterator parent_end()   const { return Parents.end(); }

	llvm::BasicBlock *getBlock() const { return TheBB; }
	size_t getNumParents() const { return Parents.size(); }
	size_t getNumChildren() const { 
		return TrueChildren.size() + FalseChildren.size() + OtherChildren.size();
	}
	bool isRegion() const { return TheBB == NULL; }
	const ControlDependenceNode *enclosingRegion() const;

private:
	llvm::BasicBlock *TheBB;
	std::set<ControlDependenceNode *> Parents;
	std::set<ControlDependenceNode *> TrueChildren;
	std::set<ControlDependenceNode *> FalseChildren;
	std::set<ControlDependenceNode *> OtherChildren;

	friend class ControlDependenceGraphBase;

	void clearAllChildren() 
	{
		TrueChildren.clear();
		FalseChildren.clear();
		OtherChildren.clear();
	}
	void clearAllParents() { Parents.clear(); }

	void addTrue(ControlDependenceNode *Child);
	void addFalse(ControlDependenceNode *Child);
	void addOther(ControlDependenceNode *Child);
	void addParent(ControlDependenceNode *Parent);
	void removeTrue(ControlDependenceNode *Child);
	void removeFalse(ControlDependenceNode *Child);
	void removeOther(ControlDependenceNode *Child);
	void removeParent(ControlDependenceNode *Child);

	ControlDependenceNode() : TheBB(NULL) {}
	ControlDependenceNode(llvm::BasicBlock *bb) : TheBB(bb) {}
};

class ControlDependenceGraphBase 
{
public:
	ControlDependenceGraphBase() : root(NULL) {}
	virtual ~ControlDependenceGraphBase() { releaseMemory(); }

	virtual void releaseMemory() 
	{
		for (ControlDependenceNode::node_iterator n = nodes.begin(), e = nodes.end();
			n != e; ++n) delete *n;
		nodes.clear();
		bbMap.clear();
		root = NULL;
	}

	void graphForFunction(llvm::Function &F, llvm::PostDominatorTree &pdt);

	ControlDependenceNode *getRoot()             { return root; }
	const ControlDependenceNode *getRoot() const { return root; }
	ControlDependenceNode *operator[](const llvm::BasicBlock *BB)             { return getNode(BB); }
	const ControlDependenceNode *operator[](const llvm::BasicBlock *BB) const { return getNode(BB); }
	ControlDependenceNode *getNode(const llvm::BasicBlock *BB) { 
		return bbMap[BB];
	}
	const ControlDependenceNode *getNode(const llvm::BasicBlock *BB) const {
		return (bbMap.find(BB) != bbMap.end()) ? bbMap.find(BB)->second : NULL;
	}
	bool controls(llvm::BasicBlock *A, llvm::BasicBlock *B) const;
	bool influences(llvm::BasicBlock *A, llvm::BasicBlock *B) const;
	const ControlDependenceNode *enclosingRegion(llvm::BasicBlock *BB) const;

private:
	ControlDependenceNode *root;
	std::set<ControlDependenceNode *> nodes;
	std::map<const llvm::BasicBlock *,ControlDependenceNode *> bbMap;
	static ControlDependenceNode::EdgeType getEdgeType(const llvm::BasicBlock *, const llvm::BasicBlock *);
	void computeDependencies(llvm::Function &F, llvm::PostDominatorTree &pdt);
	void insertRegions(llvm::PostDominatorTree &pdt);
};




#endif


