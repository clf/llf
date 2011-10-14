/**
  The type family non-terminal.  
  Represented as "P" in the official grammar spec.
  */

public interface TypeFamily extends Type {
  public BaseObject nth(int i);

  public String value() throws LLFException;
  public TypeFamily subTypeFamily() throws LLFException;
  public BaseObject subTerm() throws LLFException;
}
