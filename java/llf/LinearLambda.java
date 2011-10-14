/**
  The Linear function [x:A]M.

  This class represents linear lambda functions.
  */
public class LinearLambda implements BaseObject {
  public Variable 	x_;
  public Type		a_;
  public BaseObject	m_;

  public LinearLambda(Variable x, Type a, BaseObject m) {
    this.x_ = x;
    this.a_ = a;
    this.m_ = m;

    return;
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
    return x_;
  }
  public Type lambdaType() throws LLFException
  {
    return a_;
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
    return m_;
  }

  public int type () {
    return LINEAR_LAMBDA;
  }

  public String toString() {
    return 
      "(" +
      "[" + x_.toString() + '^' + a_.toString() + "]" + m_.toString() +
      ")";
  }

  public String astString(int i) {
    return
      Parser.space[i] + "LinearLambda" +
      x_.astString(i+2) + Parser.crlf +
      a_.astString(i+2) + Parser.crlf +
      m_.astString(i+2);
  }
}
