/**
  Type family instantiation.
  */
public class TypeFamilyInstantiation implements TypeFamily {
  private TypeFamily p_;
  private BaseObject m_;

  public TypeFamilyInstantiation(TypeFamily p, BaseObject m) {
    p_ = p;
    m_ = m;
  }
  
  public BaseObject nth(int i) {
    if (1 > i) {
      return null;
    } else if (1 == i) {
      return m_;
    } else {
      return p_.nth(i-1);
    }
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
    throw new LLFException("This method is not allowed.");
  }

  public TypeFamily subTypeFamily() throws LLFException
  {
    return p_;
  }
  public BaseObject subTerm() throws LLFException
  {
    return m_;
  }

  public int type() {
    return TYPE_FAMILY_INSTANTIATION;
  }

  public String toString () {
    return 
      "(" +
      p_.toString() + ' ' + m_.toString() +
      ")";
  }

  public String astString(int i) {
    return
      Parser.space[i] + "TypeFamilyInstantiation" + Parser.crlf +
      p_.astString(i+2) + Parser.crlf +
      m_.astString(i+2);
  }

}
