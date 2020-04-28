/* Generated By:JJTree: Do not edit this line. ASTpredSymbol.java Version 4.3 */
/* JavaCCOptions:MULTI=true,NODE_USES_PARSER=false,VISITOR=true,TRACK_TOKENS=false,NODE_PREFIX=AST,NODE_EXTENDS=,NODE_FACTORY=,SUPPORT_CLASS_VISIBILITY_PUBLIC=true */
package parser;

import java.util.HashMap;

public class ASTpredSymbol extends SimpleNode {

	public boolean negative = false;
	boolean hasPoundSign = false;

	public ASTpredSymbol(int id) {
		super(id);
	}

	public ASTpredSymbol(SparcTranslator p, int id) {
		super(p, id);
	}

	public void setPoundSign(boolean p) {
		this.hasPoundSign = p;
	}

	public boolean hasPoundSign() {
		return hasPoundSign;
	}

	/** Accept the visitor. **/
	public Object jjtAccept(SparcTranslatorVisitor visitor, Object data) {
		return visitor.visit(this, data);
	}



	public String toString() {
		StringBuilder result = new StringBuilder();
		if (negative) {
			result.append("-");
		}

	    result.append(image);
		return result.toString();
	}
	
	public String toString(HashMap<String,String> sortRenaming) {
		if(sortRenaming.containsKey(this.image) && this.hasPoundSign) {
			return toStringWithPredicateRenamed(sortRenaming.get(this.image));
		} else {
			return toString();
		}
	}

	public String toStringWithPredicateRenamed(String newName) {
		StringBuilder result = new StringBuilder();
		if (negative) {
			result.append("-");
		}
		
	    result.append(newName);
		return result.toString();
	}
}
/*
 * JavaCC - OriginalChecksum=91ab978165e8da7e3386c834953008b7 (do not edit this
 * line)
 */