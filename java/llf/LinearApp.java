/**
  A linear app.
  */
public class LinearApp implements BaseObject {
  private BaseObject left_;
  private BaseObject right_;
  
  public LinearApp(BaseObject l, BaseObject r) {
    this.left_ = l;
    this.right_ = r;
  }

  public BaseObject nth(int i) {
    if (1 > i) {
      return null;
    } else if (1 == i) {
      return right_;
    } else {
      return left_.nth(i-1);
    }
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
    return LINEAR_APP;
  }

  public String toString() {
    return "(" + this.left_ + '^' + this.right_ + ")";
  }

  public String astString(int indent) {
    return 
      Parser.space[indent] + 
      "LinearApp" + 
      Parser.crlf +
      left_.astString(indent + 2) + Parser.crlf +
      right_.astString(indent + 2);
  }

}
