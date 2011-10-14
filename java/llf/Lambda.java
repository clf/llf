/**
  The intuitionistic function [x^A]M.

  This class represents intuitionistic lambda functions
  */
public class Lambda implements BaseObject {
  private Variable 	x_;
  private Type		a_;
  private BaseObject	m_;

  public Lambda(Variable x, Type a, BaseObject m) {
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


  public int type() {
    return LAMBDA;
  }

  public String toString() {
    return 
      "(" + 
      "[" + x_.toString() + ':' + a_.toString() + "]" + m_.toString() + 
      ")";
  }

  public String astString(int i) {
    return
      Parser.space[i] + "Lambda" + Parser.crlf +
      x_.astString(i+2) + Parser.crlf +
      a_.astString(i+2) + Parser.crlf +
      m_.astString(i+2);
  }
}
