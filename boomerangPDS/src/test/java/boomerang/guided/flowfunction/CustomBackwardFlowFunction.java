package boomerang.guided.flowfunction;

import boomerang.BoomerangOptions;
import boomerang.DefaultBoomerangOptions;
import boomerang.ForwardQuery;
import boomerang.flowfunction.DefaultBackwardFlowFunction;
import boomerang.flowfunction.DefaultForwardFlowFunction;
import boomerang.scene.ControlFlowGraph.Edge;
import boomerang.scene.DeclaredMethod;
import boomerang.scene.Method;
import boomerang.scene.Statement;
import boomerang.scene.Val;
import java.util.Collection;
import java.util.Collections;
import java.util.Set;
import wpds.interfaces.State;

public class CustomBackwardFlowFunction extends DefaultBackwardFlowFunction {

  public CustomBackwardFlowFunction(DefaultBoomerangOptions opts) {
    super(opts);
  }

  @Override
  public Collection<State> callToReturnFlow(Edge edge, Val fact) {
    DeclaredMethod method = edge.getStart().getInvokeExpr().getMethod();
    //Avoid any propagations by passing the call site (also when the fact is not used at the call site).
    if(method.getDeclaringClass().getFullyQualifiedName().equals("java.lang.System") && method.getName().equals("exit")){
      return Collections.emptySet();
    }
    return super.callToReturnFlow(edge, fact);
  }

  @Override
  public Collection<Val> callFlow(Statement callSite, Val fact, Method callee, Statement calleeSp) {
    //Avoid propagations into the method when a call parameter reaches the call site
    if(callee.getDeclaringClass().getFullyQualifiedName().equals("java.lang.System") && callee.getName().equals("exit")){
      return Collections.emptySet();
    }
    return super.callFlow(callSite, fact, callee, calleeSp);
  }
}