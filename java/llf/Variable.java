/**
  A variable.

  This class represent the "v" of the official grammar spec.
*/
public class Variable implements BaseObject {
  private String name_;

  public Variable(String s) {
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
    return VARIABLE;
  }

  public String toString() {
    return name_;
  }

  public String astString(int indent) {
    return Parser.space[indent] + "Variable" + Parser.crlf +
      Parser.space[indent + 2] + this.name_;
  }
}
