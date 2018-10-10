// JavaScript source code


////////////////
// Problem 2
///////////////

var NUM = "NUM";
var FALSE = "FALSE";
var VR = "VAR";
var PLUS = "PLUS";
var TIMES = "TIMES";
var LT = "LT";
var AND = "AND";
var NOT = "NOT";

var SEQ = "SEQ";
var IFTE = "IFSTMT";
var WHLE = "WHILESTMT";
var ASSGN = "ASSGN";
var SKIP = "SKIP";
var ASSUME = "ASSUME";
var ASSERT = "ASSERT";
var HOARE = "HOARE";
var STATE = "STATE";
var SUST = "SUST";
var EMPTY = "EMPTY";
var INVARIANT = "INVARIANT";
var WHILE_INVARIANT = "WHILE_INVARIANT";
var IMPLICATION = "IMPLICATION";

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
    return { type: PLUS, left: x, right: y, toString: function () { return "(" + this.left.toString() + "+" + this.right.toString() + ")"; } };
}
function times(x, y) {
    return { type: TIMES, left: x, right: y, toString: function () { return "(" + this.left.toString() + "*" + this.right.toString() + ")"; } };
}
function lt(x, y) {
    return { type: LT, left: x, right: y, toString: function () { return "(" + this.left.toString() + "<" + this.right.toString() + ")"; } };
}
function and(x, y) {
    return { type: AND, left: x, right: y, toString: function () { 
      return "(" + this.left.toString() + "&&" + this.right.toString() + ")"; } };
}

function not(x) {
    return { type: NOT, left: x, toString: function () { return "(!" + this.left.toString() + ")"; } };
}


function seq(s1, s2) {
    return { type: SEQ, fst: s1, snd: s2, toString: function () { return "" + this.fst.toString() + ";\n" + this.snd.toString(); } };
}


function assume(e) {
    return { type: ASSUME, exp: e, toString: function () { return "assume " + this.exp.toString(); } };
}

function assert(e) {
    return { type: ASSERT, exp: e, toString: function () { return "assert " + this.exp.toString(); } };
}

function assgn(v, val) {
    return { type: ASSGN, vr: v, val: val, toString: function () { return "" + this.vr + ":=" + this.val.toString(); } };
}

function ifte(c, t, f) {
    return { type: IFTE, cond: c, tcase: t, fcase: f, toString: function () { return "if(" + this.cond.toString() + "){\n" + this.tcase.toString() + '\n}else{\n' + this.fcase.toString() + '\n}'; } };
}

function whle(c, b) {
    return { type: WHLE, cond: c, body: b, toString: function () { return "while(" + this.cond.toString() + "){\n" + this.body.toString() + '\n}'; } };
}

function skip() {
    return { type: SKIP, toString: function () { return "/*skip*/"; } };
}

function hoare(pre, command, pos) {
    return {
      type: HOARE,
      pre: pre,
      command: command,
      pos: pos,
      toString: function () {
        return "hoare(" + this.pre.toString() + ", " + this.command.toString() + ", " + pos.toString() + ")";
      }
    };
}

function state(conditions) {
    return {
      type: STATE,
      conditions: conditions,
      toString: function () {
        return "state(" + conditions.toString() + ")";
      }
    }
}

function sust(state, vr, val) {
    return {
      type: SUST,
      state: state,
      vr: vr,
      val: val,
      toString: function () {
        return "sust(" + state.toString() + ", [" + vr.toString() + " := " + val.toString() + "])";
      }
    }
}

function sust_var(command, vr, val) {
    if (command.type == VR && command.name == vr) {
        return val;
    }
    if (command.type == PLUS || command.type == TIMES || command.type == LT || command.type == AND) {
        left = sust_var(command.left, vr, val);
        right = sust_var(command.right, vr, val);
        if (command.type == PLUS)
          return plus(left, right);
        if (command.type == TIMES)
          return times(left, right);
        if (command.type == LT)
          return lt(left, right);
        if (command.type == AND)
          return and(left, right);
    }
    if (command.type == NOT) {
        return not(sust_var(command.left, vr, val));
    }
    if (command.type == ASSGN) {
        return assgn(command.vr, sust_var(command.val, vr, val));
    }
    if (command.type == IFTE) {
        return ifte(sust_var(command.cond, vr, val), sust_var(command.tcase, vr, val), sust_var(command.fcase, vr, val));
    }
    if (command.type == IMPLICATION) {
        return implication(sust_var(command.p, vr, val), sust_var(command.q, vr, val));
    }

    return command;
}

function or(x, y) {
    return not(and(not(x), not(y)))
}

function empty() {
    return {
      type: EMPTY,
      toString: function () {
        return "true";
      }
    }
}

function implication(x, y) {
    return {
      type: IMPLICATION,
      p: x,
      q: y,
      toString: function () {
        return "Implication(" + this.p.toString() + ", " + this.q.toString() + ")";
      }
    }
}

function invariant(i, vls, Q) {
    return {
      type: INVARIANT,
      index: i,
      vls: vls,
      toString: function () {
        var string = "inv_" + this.index;
        string += "(";
        if (this.vls.length > 0) {
            string +="" +  this.vls[0].toString();
        }
        for (var i = 1; i < this.vls.length; i++) {
            string += ", " + this.vls[i].toString();
        }
        string += ")"
        return string;
      },
      toString2: function () {
        var string = "inv_" + this.index;
        string += "(";
        if (this.vls.length > 0) {
            string +="int " +  this.vls[0].toString();
        }
        for (var i = 1; i < this.vls.length; i++) {
            string += ", int " + this.vls[i].toString();
        }
        string += ")"
        return string;
      }
    }
}

function while_invariant(i, invariant0, invariant1, invariant2, Q, cond, body, params) {
    return {
      type: WHILE_INVARIANT,
      index: i,
      inv0: invariant0,
      inv1: invariant1,
      inv2: invariant2,
      Q: Q,
      cond: cond,
      params: params,
      value: function () { 
        // We add all the invariants with the vars in the condition
        var and_1 = and(this.inv0, this.inv1);
        var implication_1 = implication(not(cond), Q);
        var implication_2 = implication(cond, vc(body, this.inv2).conditions);
        var and_implications = and(implication_2, implication_1);
        return implication(and_1, and_implications);
      },
      toString: function () {
        return this.value().toString();
      }
    }
}

//some useful helpers:

function eq(x, y) {
    return and(not(lt(x, y)), not(lt(y, x)));
}

function tru() {
    return not(flse());
}

function block(slist) {
    if (slist.length == 0) {
        return skip();
    }
    if (slist.length == 1) {
        return slist[0];
    } else {
        return seq(slist[0], block(slist.slice(1)));
    }
}

//The stuff you have to implement.
// Returns a list of variables that changes during the while
function getVars(command) {
    if (command.type == ASSGN) {
        return [[command.vr, command.val]];
    }
    if (command.type == SEQ) {
        fst = getVars(command.fst);
        snd = getVars(command.snd);
        return fst.concat(snd);
    }
    if (command.type == IFTE) {
        tcase = getVars(command.tcase);
        fcase = getVars(command.fcase);
        return tcase.concat(fcase);
    }
    if (command.type == WHLE) {
        body = getVars(command.body);
        return body;
    }

    return [];
}

function getVarsPre(command) {
    if (command.type == VR) {
        return [command];
    }
    if (command.type == PLUS || command.type == TIMES || command.type == LT || command.type == AND) {
        var left = getVarsPre(command.left);
        var right = getVarsPre(command.right);
        console.log("left");
        console.log(left);
        console.log("right");
        console.log(right);
        var conca = [...new Set([...left, ...right])];
        var pass = {};
        var conca_new = []
        for (var i = 0; i < conca.length; i++) {
          if (pass[conca[i].toString()] == undefined) {
              conca_new.push(conca[i]);
              pass[conca[i].toString()] = true;
          }
        }
        return conca_new;
    }
    if (command.type == NOT) {
        return getVarsPre(command.left);
    }
    return [];
}

// This function returns a State AST
function vc(command, B) {
    if (command.type == SEQ) {
        second = vc(command.snd, B);
        return vc(command.fst, second.conditions);
    }
    if (command.type == IFTE) {
        tcase = vc(command.tcase, B);
        fcase = vc(command.fcase, B);
        return state(
          or(
            and(
              command.cond,
              tcase.conditions
            ),
            and(
              not(command.cond),
              fcase.conditions
            )
          )
        );
    }
    if (command.type == WHLE) {
        // All the variables
        var all_vrs = getVarsPre(B);
        console.log(all_vrs);
        // The variables that changes in the while
        var vrs = getVars(command.body);
        var not_vrs = [];
        var params_0 = [];
        var params_1 = [];
        var params_2 = [];
        for (var i = 0; i < vrs.length; i++) {
            var finish = true;
            for (var j = 0; j < all_vrs.length; j++) {
                if (all_vrs[j].name == vrs[i][0]) {
                    finish = false;
                    break;
                }
            }
            if (finish) {
                all_vrs.push(vr(vrs[i][0]));
            }
        }
        // Create the posible params
        for (var i = 0; i < all_vrs.length; i++) {
            var finish = true;
            for (var j = 0; j < vrs.length; j++) {
                if (all_vrs[i].name == vrs[j][0]) {
                    finish = false;
                    break;
                }
            }
            if (finish) {
                not_vrs.push(all_vrs[i]);
            }
        }
        console.log(B.toString());
        for (var i = 0; i < not_vrs.length; i++) {
            params_0.push(not_vrs[i]);
            params_1.push(not_vrs[i]);
            params_2.push(not_vrs[i]);
        }
        for (var i = 0; i < vrs.length; i++) {
            params_0.push(vrs[i][0]);
            var another_var = vr(vrs[i][0] + "_p");
            params_1.push(another_var);
            var sust_var_ = sust_var(vrs[i][1], vr(vrs[i][0]), another_var);
            params_2.push(sust_var_);
        }
        // This is the while invariant
        var invariant_0 = invariant(invariant_index, params_0);
        var invariant_1 = invariant(invariant_index, params_1);
        var invariant_2 = invariant(invariant_index, params_2);
        var params = [...new Set([...params_0, ...params_1])]
        var while_invariant_ = while_invariant(invariant_index, invariant_0, invariant_1, invariant_2, B, command.cond, command.body, params);
        
        return state(while_invariant_);
        
    }
    if (command.type == ASSGN) {
        return state(sust_var(B, command.vr, command.val));
    }
    if (command.type == SKIP) {
        return state(B);
    }
    if (command.type == ASSUME) {
        return state(implication(command.exp, B));
    }
    if (command.type == ASSERT) {
        return state(and(B, command.exp));
    }
    return state(B);
}

function computeVC(prog) {
    //Compute the verification condition for the program leaving some kind of place holder for loop invariants.
	  // The input prog is an AST. The output is an AST representing the verification condition.
	  invariant_index = 0;
	  // This will write in the console the verification condition of the program.
	  // The Verification Condition answer is a state AST.
    return (vc(prog, empty()));
}

function addAssert(command) {
    var string = "";
    string += "assert "+ command.toString() +";";
    return string;
}

function printIf(impli) {
    var string = "if (" + impli.p.toString() + ") {\n"
    return string;
}

function printIfIf(impli) {
    var tab = "    ";
    var string = "";
    for (var i = 0; i < impls.length; i++) {
        string += printIf(impls[i]);
    }
    string +=printIf(impli)
    var and_ = impli.q;
    var impl_1 = and_.left;
    var impl_2 = and_.right;
    string +=printIf(impl_1);
    string +=addAssert(impl_1.q)+ "\n";
    string +="}\n"
    string +=printIf(impl_2);
    string +=addAssert(impl_2.q) + "\n";
    string +="}\n"
    string +="}\n"
    for (var i = 0; i < impls.length; i++) {
        string +="}\n"
    }
    return string;
}

function printMainFunction(while_) {
    var string = "harness void main(";
    if (while_.params.length > 0) {
        string += "int " + while_.params[0].toString();
    }
    for (var i = 1; i < while_.params.length; i++) {
        string += ", int " + while_.params[i].toString();
    }
    string += ") {";
    writeToConsole(string);
    var value = while_.value();
    string = (printIfIf(value));
    string += "}";
    writeToConsole(string);
}

function printInvFunction(command) {
    var tab = "    ";
    var string = "bit " + command.inv0.toString2() + "{\n";
    string += tab + "return exprBool({"
    if (command.inv0.vls.length > 0) {
        string +="" +  command.inv0.vls[0].toString();
    }
    for (var i = 1; i < command.inv0.vls.length; i++) {
        string += ", " + command.inv0.vls[i].toString();
    }
    string += "}, {PLUS});";
    string += "\n";
    string += "}";
    return string;
}

function auxSketch(command) {
    if (command.type == WHILE_INVARIANT) {
        printMainFunction(command);
        writeToConsole("\n");
        writeToConsole(printInvFunction(command));
    }
    if (command.type == PLUS || command.type == TIMES || command.type == LT || command.type == AND) {
        auxSketch(command.left);
        auxSketch(command.right);
    }
    if (command.type == NOT) {
        auxSketch(command.left);
    }
    if (command.type == IMPLICATION) {
        impls.push(command);
        auxSketch(command.q);
    }
}

function genSketch(vc_) {
    //Write a pretty printer that generates a sketch from the verification condition.
    //You can write your generators as a separate library, but you may do better by creating generators specialized for your problem.
	  //The input is the VC that was generated by computeVC. The output is a String 
	  //representing the sketch that you can feed to the sketch solver to synthesize the invariants.
	  impls = [];
	  auxSketch(vc_.conditions);
}



function P2a() {
    var prog = eval(document.getElementById("p2input").value);
    var vc_ = computeVC(prog);
    writeTo
    writeToConsole("\nTEST 1\n");
    test1_a();
    writeToConsole("\nTEST 2\n");
    test2_a();
    /*
    clearConsole();
    writeToConsole("Just pretty printing for now");
    writeToConsole(prog.toString());
    */
}

function P2b() {
    var prog = eval(document.getElementById("p2input").value);
    genSketch(computeVC(prog));
    writeToConsole("\n");
    writeToConsole("TEST 1");
    writeToConsole("\n");
    test1_b();
    writeToConsole("\nTEST 2\n");
    test2_b();
}


//Some functions you may find useful:
function randInt(lb, ub) {
    var rf = Math.random();
    rf = rf * (ub - lb) + lb;
    return Math.floor(rf);
}

function randElem(from) {
    return from[randInt(0, from.length)];
}

function writeToConsole(text) {
    var csl = document.getElementById("console");
    if (typeof text == "string") {
        csl.textContent += text + "\n";
    } else {
        csl.textContent += text.toString() + "\n";
    }
}

function clearConsole() {
    var csl = document.getElementById("console");
    csl.textContent = "";
}

function test1_a() {
    var prog1 = block([
        assume(tru()),
        whle(lt(vr('x'), num(10)),
            block([
                block([
                assgn('x', plus(vr('x'),num(1))),
                ])
            ])
        ),
        assert(eq(vr('x'), vr('y')))
    ]);
    var vc_ = computeVC(prog1);
    writeToConsole(vc_.toString());
}

function test1_b() {
    var prog1 = block([
        assume(tru()),
        whle(lt(vr('x'), num(10)),
            block([
                block([
                assgn('x', plus(vr('x'),num(1))),
                ])
            ])
        ),
        assert(eq(vr('x'), vr('y')))
    ]);
    var vc_ = computeVC(prog1);
    genSketch(vc_);
}

function test2_a() {
    var prog1 = block([
        assume(and(eq(vr("y"),vr("y_0")), and(eq(vr("k"),vr("k_0")), eq(vr("t"),plus(vr("y_0"),vr("k_0")))))),
        whle(lt(vr('t'), num(10)),
            block([
                assgn('y', plus(vr('y'),num(1))),
                assgn('t', plus(vr('t'),num(1))),
            ])
        ),
        assert(lt(vr("y"), vr("k_0")))
    ]);
    var vc_ = computeVC(prog1);
    writeToConsole(vc_.toString());
}

function test2_b() {
    var prog1 = block([
        assume(and(eq(vr("y"),vr("y_0")), and(eq(vr("k"),vr("k_0")), eq(vr("t"),plus(vr("y_0"),vr("k_0")))))),
        whle(lt(vr('t'), num(10)),
            block([
                assgn('y', plus(vr('y'),num(1))),
                assgn('t', plus(vr('t'),num(1))),
            ])
        ),
        assert(eq(("y_0"), vr("y_0"))),
        assert(eq(vr("k_0"), vr("k_0"))),
        assert(eq(vr("k"), vr("k"))),
        assert(lt(vr("y"), vr("k_0")))
    ]);
    var vc_ = computeVC(prog1);
    genSketch(vc_);
}