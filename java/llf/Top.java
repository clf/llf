/**
  Top.
  */
public class Top implements Type {
  public Top() 
  {
    return;
  }

  public Variable variable() throws LLFException
  {
    throw new LLFException("This method is not allowed.");
  }
  public Type leftSubterm()  throws LLFException
  {
    throw new LLFException("This method is not allowed.");
  }
  public Type rightSubterm() throws LLFException
  {
    throw new LLFException("This method is not allowed.");
  }

  public int type() {
    return TOP;
  }

  public String toString() {
    return "<T>";
  }

  public String astString(int i) {
    return
      Parser.space[i] + "Top";
  }
}
