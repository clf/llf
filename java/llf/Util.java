import java.util.Vector;

public class Util 
{
  public static void head(BaseObject bo, Vector ret) 
    {
      try {
	if (bo instanceof Identifier) {
	  ret.addElement(bo);
	} 
	
	if (bo instanceof Variable) {
	  ret.addElement(bo);
	} 
	
	else if (bo instanceof Lambda) {
	  Lambda m = (Lambda) bo;
	  head(m.subterm(), ret);
	}
	
	else if (bo instanceof App) {
	  App m = (App) bo;
	  head(m.leftSubterm(), ret);
	}
	
	else if (bo instanceof LinearLambda) {
	  LinearLambda m = (LinearLambda) bo;
	  head(m.subterm(), ret);
	}
	
	else if (bo instanceof LinearApp) {
	  LinearApp m = (LinearApp) bo;
	  head(m.leftSubterm(), ret);
	}
	
	else if (bo instanceof Pair) {
	  Pair m = (Pair) bo;
	  head(m.leftSubterm(), ret);	
	  head(m.rightSubterm(), ret);
	}
	
	else if (bo instanceof First) {
	  First m = (First) bo;
	  head(m.subterm(), ret);
	}
	
	else if (bo instanceof Second) {
	  Second m = (Second) bo;
	  head(m.subterm(), ret);
	}
	
	else if (bo instanceof Unit) {
	  Unit m = (Unit) bo;
	}
      } catch (LLFException llfe) {
	// Should never occur as long as we use everything correctly.
	llfe.printStackTrace();
      }
      return;
    }

}
