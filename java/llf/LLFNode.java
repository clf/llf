/**
   The top level interface for all AST nodes.
 */
public interface LLFNode {
  public String astString(int indent);


  public int type();

  public static final int APP = 		2;
  public static final int FIRST =		3;
  public static final int FUNCTION_TYPE =	4;
  public static final int IDENTIFIER =		5;
  public static final int LAMBDA =		6;
  public static final int LINEAR_APP =		7;
  public static final int LINEAR_LAMBDA =	8;
  public static final int LOLLIPOP =		9;
  public static final int PAIR =		10;
  public static final int SECOND =		11;
  public static final int TOP =			12;
  public static final int TYPE_FAMILY_CONSTANT =13;
  public static final int TYPE_FAMILY_INSTANTIATION = 14;
  public static final int UNIT =		15;
  public static final int VARIABLE =		16;
  public static final int WITH =		17;

}
