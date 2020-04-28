/* Generated By:JJTree: Do not edit this line. ASTaggregate.java Version 4.3 */
/* JavaCCOptions:MULTI=true,NODE_USES_PARSER=false,VISITOR=true,TRACK_TOKENS=false,NODE_PREFIX=AST,NODE_EXTENDS=,NODE_FACTORY=,SUPPORT_CLASS_VISIBILITY_PUBLIC=true */
package parser;

import java.util.HashMap;

public
class ASTaggregate extends SimpleNode {
  public ASTaggregate(int id) {
    super(id);
  }

  public ASTaggregate(SparcTranslator p, int id) {
    super(p, id);
  }


  /** Accept the visitor. **/
  public Object jjtAccept(SparcTranslatorVisitor visitor, Object data) {
    return visitor.visit(this, data);
  }
  
  
  // disallow toString() call without sort renaming map
  @Override
  public String toString() {
	  throw new UnsupportedOperationException();
  }
  
  
  public String toString(HashMap<String,String> sortRenaming) {
	  //[arithmeticTerm() t1=rel()] aggregateFunction()
	  //< OB > aggregateElements()
	  //< CB > [t2=rel() arithmeticTerm()]
	  StringBuilder sb=new StringBuilder();
	  int curIndex=0;
	  if(this.image.indexOf('L')!=-1) {
		 int lastLIndex=this.image.indexOf('R');
		 if(lastLIndex==-1) lastLIndex=this.image.length();
		 ASTarithmeticTerm arLterm=(ASTarithmeticTerm)this.jjtGetChild(curIndex);
		 ++curIndex;
		 sb.append(arLterm.toString());
		 sb.append(this.image.substring(this.image.indexOf('L')+1,lastLIndex));
	  }
	  sb.append(((ASTaggregateFunction)this.jjtGetChild(curIndex)).toString());
	  ++curIndex;
	  sb.append(((ASTaggregateElements)this.jjtGetChild(curIndex)).toString(sortRenaming));
	  ++curIndex;
	  sb.append("}");
	  if(this.image.indexOf('R')!=-1) {
			 int lastLIndex=this.image.length();
			 ASTarithmeticTerm arLterm=(ASTarithmeticTerm)this.jjtGetChild(curIndex);
			 ++curIndex;
			 sb.append(this.image.substring(this.image.indexOf('R')+1,lastLIndex));
			 sb.append(arLterm.toString());
	   }
	  return sb.toString();
  }
}
/* JavaCC - OriginalChecksum=cb2f5f12e4abaf2a829aa08625043720 (do not edit this line) */