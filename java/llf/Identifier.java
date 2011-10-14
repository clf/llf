/**
  A variable or constant.

  This class represent the "v" or "c" of the official grammar spec.
*/
public class Identifier implements BaseObject {
  private String name_;

  public Identifier(String s) {
    this.name_ = s;
  }

  public BaseObject nth(int i) {
    return null;
  }

  public String value() throws LLFException
  {
    return name_;
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
    return IDENTIFIER;
  }

  public String toString() {
    return name_;
  }

  public String astString (int i) {
    return 
      Parser.space[i] + "Identifier" + Parser.crlf +
      Parser.space[i+2] + name_;
      
  }
}
