public class Example {
  public static void main(String args[]) throws ParseException {
    BaseObject o;

    if (0 == args.length) {
      System.out.println("Enter your expression here:");

      Parser p = Parser.create(System.in);
      o = p.root();
    } else {
      System.out.println("Taking expression from the command line.");
      
      Parser p = Parser.create(args[0]);
      o = p.root();
    }

    System.out.println("This is the ast output:::");
    System.out.println(o.astString(0));	

    System.out.println("This is the output:::");
    System.out.println(o);	

    System.out.println("This is the head:::");
    java.util.Vector v = new java.util.Vector();  
    Util.head(o, v);
    System.out.println(v);
  }
}
