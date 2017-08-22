package sync.pds.solver;

import sync.pds.solver.nodes.Node;

public interface WitnessListener<Stmt,Fact> {

	void witnessFound(Node<Stmt, Fact> targetFact);

}