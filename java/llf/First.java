/**
  First.
  */
public class First implements BaseObject {
  private BaseObject bo_;
  
  public First(BaseObject bo) {
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
    return FIRST;
  }

  public String toString() {
    return 
      "(" +
      "<fst>" + this.bo_ +
      ")";
  }

  public String astString(int indent) {
    return 
      Parser.space[indent] + "First" + Parser.crlf +
      this.bo_.astString(indent + 2);
  }
}
