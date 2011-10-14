/**
   This is the base object interface.  It is also the top level.
*/
public interface BaseObject extends LLFNode {
  BaseObject nth(int i);

  public String value() throws LLFException;
  public Variable variable() throws LLFException;
  public Type lambdaType() throws LLFException;
  public BaseObject leftSubterm() throws LLFException;
  public BaseObject rightSubterm() throws LLFException;
  public BaseObject subterm() throws LLFException;

}
