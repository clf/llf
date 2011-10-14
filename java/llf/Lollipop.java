/**
  Linear function types.
  */
public class Lollipop implements Type {
  private Type left_;
  private Type right_;

  public Lollipop(Type l, Type r) {
    this.left_ = l;
    this.right_ = r;
  }

  public Variable variable() throws LLFException
  {
    throw new LLFException("This method is not allowed.");
  }
  public Type leftSubterm()  throws LLFException
  {
    return left_;
  }
  public Type rightSubterm() throws LLFException
  {
    return right_;
  }

  public int type() {
    return LOLLIPOP;
  }

  public String toString () {
    return "(" + left_ + " -o " + right_ + ")";
  }

  public String astString(int indent) {
    return 
      Parser.space[indent] + "Lollipop" + Parser.crlf +
      left_.astString(indent + 2) + Parser.crlf +
      right_.astString(indent + 2);
  }

}
