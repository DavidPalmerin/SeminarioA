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

// Gives prob and returns the expression and its probability
function assignProbs(exp, probs) {
    table = {exp: exp}
    for (var i = 0; i < probs.length; i++) {
        table["p" + i.toString()] = probs[i];
    }
    return table;
}

function getAllProbs(exp, prob) {
    var probs = [];
    probs.push(prob(exp.type, 0, null)); // Root
    probs.push(prob(exp.type, 0, PLUS));
    probs.push(prob(exp.type, 1, PLUS));
    probs.push(prob(exp.type, 0, TIMES));
    probs.push(prob(exp.type, 1, TIMES));
    probs.push(prob(exp.type, 0, LT));
    probs.push(prob(exp.type, 1, LT));
    probs.push(prob(exp.type, 0, AND));
    probs.push(prob(exp.type, 1, AND));
    probs.push(prob(exp.type, 0, NOT));
    probs.push(prob(exp.type, 0, ITE));
    probs.push(prob(exp.type, 1, ITE));
    probs.push(prob(exp.type, 2, ITE));
    return probs;
}

function mapExpPos(exp, pos) {
    if (exp.type == PLUS)
        return 1 + pos;
    if (exp.type == TIMES)
        return 3 + pos;
    if (exp.type == LT)
        return 5 + pos;
    if (exp.type == AND)
        return 7 + pos;
    if (exp.type == NOT)
        return 9;
    if (exp.type == ITE)
        return 10 + pos;
    return 0;
}


function getExpProb(table, exp, pos) {
    return table["p" + mapExpPos(exp, pos).toString()];
}


function getActualTable(table, item1, item2, item3, prob) {
    var actual_prob = getExpProb(item1, table, 0);
    if (item2 != null) {
        actual_prob *= getExpProb(item2, table, 1);
    }
    if (item3 != null) {
        actual_prob *= getExpProb(item3, table, 2);
    }
    var probs = getAllProbs(table, prob);
    for (var i = 0; i < 13; i++) {
        probs[i] *= actual_prob;
    }
    return assignProbs(table, probs);
}

function possible(table) {
    for (var i = 0; i < 13; i++) {
        if (table["p" + i.toString()] > 0)
            return true;
    }
    return false;
}

function isCorrect(program, inputoutputs) {
    var count = 0
    for (var j = 0; j < inputoutputs.length; j++) {
        if (interpret(program, inputoutputs[j]) == inputoutputs[j]._out) {
            count += 1;
        } else {
            break;
        } 
    }
    if (inputoutputs.length == count) {
        /*console.log(interpret(program, inputoutputs[0]));
        console.log(inputoutputs[0]._out);
        console.log(interpret(program, inputoutputs[1]));
        console.log(inputoutputs[1]._out);*/
        return true;
    }
    return false;
}


function grow(intOps, boolOps, vars, consts, tables, inputoutputs, prob) {
    var actual_prob = 1;
    var new_exp = null;
    var actual_level = [];
    var actual_table = null;
    boolOps.forEach(function(item, index) {
        if (item == LT) {
            tables.forEach(function(item1, index1) {
                tables.forEach(function(item2, index2) {
                    new_exp = lt(item1.exp, item2.exp);
                    actual_table = getActualTable(new_exp, item1, item2, null, prob);
                    if (possible(actual_table)) {    
                        actual_level.push(actual_table);
                        checkBest(table, inputoutputs);
                    }
                });
            });
        } else if (item == AND) {
            tables.forEach(function(item1, index1) {
                tables.forEach(function(item2, index2) {
                    new_exp = and(item1.exp, item2.exp);
                    actual_table = getActualTable(new_exp, item1, item2, null, prob);
                    if (possible(actual_table)) {    
                        actual_level.push(actual_table);
                        checkBest(actual_table, inputoutputs);
                    }
                });
            });
        } else if (item == NOT) {
            tables.forEach(function(item1, index1) {
                new_exp = not(item1.exp);
                actual_table = getActualTable(new_exp, item1, null, null, prob);
                if (possible(actual_table)) {    
                    actual_level.push(actual_table);
                    checkBest(actual_table, inputoutputs);
                }
            });
        }
    });
    intOps.forEach(function(item, index) {
        if (item == PLUS) {
            tables.forEach(function(item1, index1) {
                tables.forEach(function(item2, index2) {
                    new_exp = plus(item1.exp, item2.exp);
                    actual_table = getActualTable(new_exp, item1, item2, null, prob);
                    if (possible(actual_table)) {    
                        actual_level.push(actual_table);
                        checkBest(actual_table, inputoutputs);
                    }
                });
            });
        } else if (item == TIMES) {
            tables.forEach(function(item1, index1) {
                tables.forEach(function(item2, index2) {
                    new_exp = and(item1.exp, item2.exp);
                    actual_table = getActualTable(new_exp, item1, item2, null, prob);
                    if (possible(actual_table)) {    
                        actual_level.push(actual_table);
                        checkBest(actual_table, inputoutputs);
                    }
                });
            });
        } else if (item == ITE) {
            tables.forEach(function(item1, index1) {
                tables.forEach(function(item2, index2) {
                    tables.forEach(function(item3, index3) {
                        new_exp = ite(item1.exp, item2.exp, item3.exp);
                        actual_table = getActualTable(new_exp, item1, item2, item3, prob);
                        if (possible(actual_table)) {    
                            actual_level.push(actual_table);
                            checkBest(actual_table, inputoutputs);
                        }
                    });
                });
            });
        }
    });
    return actual_level;
}


function checkBest(table, inputoutputs) {
    if (isCorrect(table.exp, inputoutputs)) {
        //console.log(table.exp);
        if (best_prob < table.p0) {
            best_prob = table.p0;
            best_table = table;
        }
    }
}

function elimEquivalents(tables, inputs) {
    var outputs = {};
    var newtables = []
    tables.forEach(function(item, index) {
        var outputsStr = "";
        inputs.forEach(function(input, indexIn) {
            outputsStr += interpret(item.exp, input).toString() + " | ";
        });
        if (outputs[outputsStr] === undefined) {
            outputs[outputsStr] = index;
            newtables.push(item);
        }
    });
    return newtables;
}


function bottomUp(globalBnd, intOps, boolOps, vars, consts, inputoutputs, prob) {
    var tables = [];
    var actual_table = null;
    best_prob = 0;
    best_table = null;
    vars.forEach(function(item1, index1) {
        actual_table = assignProbs(vr(item1), getAllProbs(vr(item1), prob));
        tables.push(actual_table);
        checkBest(actual_table, inputoutputs);
    });
    consts.forEach(function(item1, index1) {
        actual_table = assignProbs(num(item1), getAllProbs(num(item1), prob));
        tables.push(actual_table);
        checkBest(actual_table, inputoutputs);
    });
    actual_table = assignProbs(flse(), getAllProbs(flse(), prob));
    tables.push(actual_table);
    checkBest(actual_table, inputoutputs);
    // While true
	console.log("Working");
    for (var i = 0; i < globalBnd; i++) {
        // grow list
        console.log("Bound: " + i.toString());
        newLevel = grow(intOps, boolOps, vars, consts, tables, inputoutputs, prob);
        tables = tables.concat(newLevel);
        tables = elimEquivalents(tables, inputoutputs);
        //console.log(tables);
    }
    console.log(best_table);
	return best_table.exp;
}


function run2(){
	
	function prob(child, id, parent){
		//Example of a probability function. In this case, the function
		//has uniform distributions for most things except for cases that would
		//cause either type errors or excessive symmetries.
		//You want to make sure your solution works for arbitrary probability distributions.
		
		function unif(possibilities, kind){
			if(possibilities.includes(kind)){
				return 1.0/possibilities.length;
			}
			return 0;
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
	        	return unif([LT, AND, NOT, FALSE], child);
	        	break;
	        case NOT:
	        	return unif([LT, AND, FALSE], child);
	        	break;
	        case ITE:
	        	if(id == 0)
	        		return unif([LT, AND, FALSE, NOT], child);					
				else
					return unif([NUM, VR, PLUS, TIMES, ITE], child);
	        	break;
	        case null:
	            return 0.11;
		}
	}
	
	
	var rv = bottomUp(3, [VR, NUM, PLUS, TIMES, ITE], 
			             [AND, NOT, LT, FALSE], ["x", "y"], [4, 5], 
			             [{x:5,y:10, _out:5},{x:8,y:3, _out:3}], 
			             prob
	);
	writeToConsole("RESULT: " + rv.toString());
	
}

