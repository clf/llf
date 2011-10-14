/**
  Second.
  */
public class Second implements BaseObject {
  private BaseObject bo_;
  
  public Second(BaseObject bo) {
    this.bo_ = bo;
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
    return bo_;
  }
  public int type() {
    return SECOND;
  }

  public String toString() {
    return 
      "(" +
      "<snd>" + this.bo_ +
      ")";
  }

  public String astString(int indent) {
    return 
      Parser.space[indent] + "Second" + Parser.crlf +
      this.bo_.astString(indent + 2);
  }
}
