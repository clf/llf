/**
  Type family constants.
  */
public class TypeFamilyConstant implements TypeFamily {
  private String name_;

  public TypeFamilyConstant(String s) {
    name_ = s;
  }

  public BaseObject nth(int i) {
    return null;
  }

  public Variable variable() throws LLFException
  {
    throw new LLFException("This method is not allowed.");
  }
  public Type leftSubterm()  throws LLFException
  {
    throw new LLFException("This method is not allowed.");
  }
  public Type rightSubterm() throws LLFException
  {
    throw new LLFException("This method is not allowed.");
  }

  public String value() throws LLFException
    {
      return name_;
    }

  public TypeFamily subTypeFamily() throws LLFException
    {
      throw new LLFException("This method is not allowed.");
    }

  public BaseObject subTerm() throws LLFException
    {
      throw new LLFException("This method is not allowed.");
    }

  public int type() {
    return TYPE_FAMILY_CONSTANT;
  }

  public String toString() {
    return name_;
  }

  public String astString(int i) {
    return 
      Parser.space[i] + "TypeFamilyConstant" + Parser.crlf +
      Parser.space[i+2] + name_;
  }
}
