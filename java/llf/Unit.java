/**
  A Unit.  "<>".
  */
public class Unit implements BaseObject {
  public Unit() {
  }

  public BaseObject nth(int i) {
    return null;
  }

  public String value() throws LLFException
  {
    throw new LLFException("This method is not supported.");
  }
  public Variable variable() throws LLFException
  {
    throw new LLFException("This method is not supported.");
  }
  public Type lambdaType() throws LLFException
  {
    throw new LLFException("This method is not supported.");
  }
  public BaseObject leftSubterm() throws LLFException
  {
    throw new LLFException("This method is not supported.");
  }
  public BaseObject rightSubterm() throws LLFException
  {
    throw new LLFException("This method is not supported.");
  }
  public BaseObject subterm() throws LLFException
  {
    throw new LLFException("This method is not supported.");
  }

  public int type() {
    return UNIT;
  }

  public String toString() {
    return "<>";
  }

  public String astString(int indent) {
    return 
      Parser.space[indent] + "Unit";
  }  
}
