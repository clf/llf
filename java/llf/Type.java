/**
  The type non-terminal.  Represented as "A" in the official grammar spec.
  */

public interface Type extends LLFNode {
  public Variable variable() throws LLFException;
  public Type leftSubterm()  throws LLFException;
  public Type rightSubterm() throws LLFException;
}
