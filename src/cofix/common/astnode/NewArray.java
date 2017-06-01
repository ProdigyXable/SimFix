/**
 * Copyright (C) SEI, PKU, PRC. - All Rights Reserved.
 * Unauthorized copying of this file via any medium is
 * strictly prohibited Proprietary and Confidential.
 * Written by Jiajun Jiang<jiajun.jiang@pku.edu.cn>.
 */
package cofix.common.astnode;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.Type;

/**
 * @author Jiajun
 * @datae May 31, 2017
 */
public class NewArray extends MethodCall{

	private List<Expr> _dimension = null;
	private List<Expr> _initializers = null;
	
	public NewArray(ASTNode node, Type retType, Expr expr, String name) {
		this(node, retType, expr, name, new ArrayList<>());
	}
	
	public NewArray(ASTNode node, Type retType, Expr expr, String name, List<Expr> dimensions){
		this(node, retType, expr, name, dimensions, null);
	}
	
	public NewArray(ASTNode node, Type retType, Expr expr, String name, List<Expr> dimensions, List<Expr> initializers){
		super(node, retType, expr, name);
		_dimension = dimensions;
		_initializers = initializers;
	}
	
	public void setDimension(List<Expr> dimension){
		_dimension = dimension;
	}
	
	public void setInitializers(List<Expr> initializers){
		_initializers = initializers;
	}
	
	@Override
	public String toString() {
		StringBuffer stringBuffer = new StringBuffer();
		if(_expr != null){
			stringBuffer.append(_expr);
			stringBuffer.append(".");
		}
		stringBuffer.append("new ");
		stringBuffer.append(_name);
		for(int i = 0; i < _dimension.size(); i++){
			stringBuffer.append("[");
			stringBuffer.append(_dimension.get(i));
			stringBuffer.append("]");
		}
		if(_initializers != null){
			stringBuffer.append("{");
			stringBuffer.append(_initializers.get(0));
			for(int i = 1; i < _initializers.size(); i++){
				stringBuffer.append(",");
				stringBuffer.append(_initializers.get(i));
			}
			stringBuffer.append("}");
		}
		return stringBuffer.toString();
	}
	

}
