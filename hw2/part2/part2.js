// JavaScript source code

var NUM = "NUM";
var FALSE = "FALSE";
var VR = "VAR";
var PLUS = "PLUS";
var TIMES = "TIMES";
var LT = "LT";
var AND = "AND";
var NOT = "NOT";
var ITE = "ITE";

var ALLOPS = [NUM, FALSE, VR, PLUS, TIMES, LT, AND, NOT, ITE];

function str(obj) { return JSON.stringify(obj); }

//Constructor definitions for the different AST nodes.

function flse() {
    return { type: FALSE, toString: function () { return "false"; } };
}

function vr(name) {
    return { type: VR, name: name, toString: function () { return this.name; } };
}
function num(n) {
    return { type: NUM, val: n, toString: function () { return this.val; } };
}
function plus(x, y) {
    return { type: PLUS, left: x, right: y, toString: function () { return "("+ this.left.toString() + "+" + this.right.toString()+")"; } };
}
function times(x, y) {
    return { type: TIMES, left: x, right: y, toString: function () { return "(" + this.left.toString() + "*" + this.right.toString() + ")"; } };
}
function lt(x, y) {
    return { type: LT, left: x, right: y, toString: function () { return "(" + this.left.toString() + "<" + this.right.toString() + ")"; } };
}
function and(x, y) {
    return { type: AND, left: x, right: y, toString: function () { return "(" + this.left.toString() + "&&" + this.right.toString() + ")"; } };
}
function not(x) {
    return { type: NOT, left: x, toString: function () { return "(!" + this.left.toString()+ ")"; } };
}
function ite(c, t, f) {
    return { type: ITE, cond: c, tcase: t, fcase: f, toString: function () { return "(if " + this.cond.toString() + " then " + this.tcase.toString() + " else " + this.fcase.toString() + ")"; } };
}

//Interpreter for the AST.
function interpret(exp, envt) {
    switch (exp.type) {
        case FALSE: return false;
        case NUM: return exp.val;
        case VR: return envt[exp.name];
        case PLUS: return interpret(exp.left, envt) + interpret(exp.right, envt);
        case TIMES: return interpret(exp.left, envt) * interpret(exp.right, envt);
        case LT: return interpret(exp.left, envt) < interpret(exp.right, envt);
        case AND: return interpret(exp.left, envt) && interpret(exp.right, envt);
        case NOT: return !interpret(exp.left, envt);
        case ITE: if (interpret(exp.cond, envt)) { return interpret(exp.tcase, envt); } else { return interpret(exp.fcase, envt); }
    }
}

function writeToConsole(text) {
    var csl = document.getElementById("console");
    if (typeof text == "string") {
        csl.value += text + "\n";
    } else {
        csl.value += text.toString() + "\n";
    }
}


function bottomUp(globalBnd, intOps, boolOps, vars, consts, inputoutputs, prob) {
    
	return "NYI";
}


function run2(){
	
	function prob(child, id, parent){
		//Example of a probability function. In this case, the function
		//has uniform distributions for most things except for cases that would
		//cause either type errors or excessive symmetries.
		//You want to make sure your solution works for arbitrary probability distributions.
		
		function unif(possibilities, kind){
			if(kind in possibilities){
				return 1.0/possibilities.length;
			}
		}
		
		switch(parent){
			case PLUS: 
				if(id == 0)
					return unif([NUM, VR, PLUS, TIMES, ITE], child);
				else
					return unif([NUM, VR, TIMES, ITE], child);
				break;
	        case TIMES: 
	        	if(id == 0)
					return unif([NUM, VR, PLUS, TIMES, ITE], child);
				else
					return unif([NUM, VR, ITE], child);
	        	break;	        	
	        case LT: 
	        	return unif([NUM, VR, PLUS, TIMES, ITE], child);
	        	break;
	        case AND:
	        	return unif([LT, AND, NOT], child);
	        	break;
	        case NOT:
	        	return unif([LT, AND], child);
	        	break;
	        case ITE:
	        	if(id == 0)
	        		return unif([LT, AND], child);					
				else
					return unif([NUM, VR, PLUS, TIMES, ITE], child);
	        	break;
		}
	}
	
	
	var rv = bottomUp(3, [VR, NUM, PLUS, TIMES, ITE], 
			             [AND, NOT, LT, FALSE], ["x", "y"], [4, 5], 
			             [{x:5,y:10, _out:5},{x:8,y:3, _out:3}], 
			             prob
	);
	writeToConsole("RESULT: " + rv.toString());
	
}

