/**
  Intuitionistic function types.
  */
public class FunctionType implements Type {
  private Variable x_;
  private Type left_;
  private Type right_;

  public FunctionType(Variable x, Type l, Type r) {
    this.x_ = x;
    this.left_ = l;
    this.right_ = r;
  }

  public Variable variable() throws LLFException
  {
    return x_;
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
    return FUNCTION_TYPE;
  }

  public String toString () {
    return "{" + x_ + ":" + left_ + "}" + right_;
  }

  public String astString(int i) {
    return
      Parser.space[i] + "FunctionType" + Parser.crlf +
      ((null == x_) ? (Parser.space[i] + "(null)" + Parser.crlf) : 
      		     (x_.astString(i+2) + Parser.crlf)) +
      left_.astString(i+2) + Parser.crlf +
      right_.astString(i+2);
  }
}
