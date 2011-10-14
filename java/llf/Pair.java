/**
  An additive pair.
  */
public class Pair implements BaseObject {
  private BaseObject left_;
  private BaseObject right_;
  
  public Pair(BaseObject l, BaseObject r) {
    this.left_ = l;
    this.right_ = r;
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
    return left_;
  }
  public BaseObject rightSubterm() throws LLFException
  {
    return right_;
  }
  public BaseObject subterm() throws LLFException
  {
    throw new LLFException("This method is not supported.");
  }

  public int type() {
    return PAIR;
  }

  public String toString() {
    return "(" + this.left_ + ',' + this.right_ + ")";
  }

  public String astString(int indent) {
    return 
      Parser.space[indent] + "Pair" + Parser.crlf +
      left_.astString(indent + 2) + Parser.crlf +
      right_.astString(indent + 2);
  }

}
