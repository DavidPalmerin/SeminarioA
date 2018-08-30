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

var ALLOPS =  [NUM, FALSE, VR, PLUS, TIMES, LT, AND, NOT, ITE];
var INTOPS =  [NUM, PLUS, TIMES];
var BOOLOPS = [FALSE, LT, AND, NOT];

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
        csl.value += text + "\n";
    } else {
        csl.value += text.toString() + "\n";
    }
}


function bottomUp(globalBnd, intOps, boolOps, vars, consts, inputoutputs) {
    observationalTable = {};
    programs = []
    insertVariables(programs, vars);
    insertConstants(programs, consts);

    //while (globalBnd > 0) {
        programs = grow(programs, intOps, boolOps);

        globalBnd--;
    //}

   
    return "NYI";
}

function operator_arity(op) {
    if (op == FALSE) return 0;
    if (op == VR || op == NUM || op == NOT) return 1;
    if (op == ITE) return 3;
    return 2;
}

function validParams(params, validOptions) {
    for (var i = 0; i < params.length; i++) {
        if (!(params[i].type in validOptions))
            return false;
    }
    return true;
}

// checarbien esta funcion, como en not.
// Falta ver caso especial de ITE. (Que coincidan en tipo los dos ultimos parametros, y que 
// el primero sea booleano).
// Y agregar caso especial para variables en validParams. (Pues vr puede ser numerico).
function createNewProgram(op, params) {
    switch(op) {
        case PLUS:
            if (validParams(params, INTOPS))
                return plus(params[0], params[1]);
            break;
        case TIMES:
            if (validParams(params, INTOPS))
                return times(params[0], params[1]);
            break;
        case LT:
            if (validParams(params, INTOPS))
                return lt(params[0], params[1]);
            break;
        case AND:
            if (validParams(params, BOOLOPS))
                return and(params[0], params[1]);
            break;
        case NOT:
            if (validParams(params, BOOLOPS))
                return not(params[0]);
            break;
        case ITE:
            if (validParams(params[0], BOOLOPS))
                return ite(params[0], params[1], params[2]);
            break;
        case NUM:
            if (typeof params[0] == typeof 0)
                return num(params[0]);
            break;
        case VR:
            if (typeof params[0] == typeof(" "))
                return vr(params[0]);
            break;
        case FALSE:
            return flse();
    }

    return null;
}

function myfun() {
    programs = [plus(times(num(2), num(3)), num(2)), lt(num(2), num(5))];
    newPrograms = grow(programs, INTOPS, BOOLOPS);
    writeToConsole(newPrograms.length);
    newPrograms.forEach(function(p) { console.log(p); } );
}


//Es mejor generr las permutaiones fuera del while de donde se llama.
function grow(programs, intOps, boolOps) {
    var newPrograms = [];
    permutations = genPermutations(programs.length, 3); // Since three is the maximum arity for operators in this grammar.
    for (var i = 0; i < intOps.length; i++) {
        op = intOps[i];
        arity = operator_arity(op);
        arity_perms = permutations[arity];
        for (var j = 0; j < arity_perms.length; j++) {
            var params  = arity_perms[j].map(function(index) { return programs[index]; });
            var synth_program = createNewProgram(op, params);
            if (synth_program != null)
                newPrograms.push(synth_program);
        }
    }   
    return newPrograms;
}

// All the permutations for 0 to n - 1 of length <= k.
function genPermutations(n, k) {
    var queue = [];
    for (var i = 0; i < n; i++) queue.push([i]);

    var permutations = {};
    while (queue.length > 0 && queue[0].length <= k) {
        var ls = queue.shift();
        if (!(ls.length in permutations)) 
            permutations[ls.length] = [ls];
        else permutations[ls.length].push(ls);
        
        last = ls[ls.length - 1];
        for (i = (last + 1) % n; i < n; i++)
            queue.push(ls.concat([i]));
    }   

    return permutations;
}

function insertConstants(programs, consts) {
    for (i = 0; i < consts.length; i++)
        programs.push(num(consts[i]));
}

function insertVariables(programs, vars) {
    for (i = 0; i < vars.length; i++) 
        programs.push(vr(vars[i]));
}

// Deletes equivalent programs based on obsevational equivalence.
// observationalTable is a dictionary which key is the answer evaluated with a program p.
function elimEquivalents(programs, observationalTable, inputs) {
    newPrograms = []
    for (i = 0; i < programs.length; i++) {
        program = programs[i];
        for (j = 0; j < inputs.length; j++) {
            envt = input[j];
            ans = interpret(program, envt);
            if (! ans in observationalTable) { 
                observationalTable.push({ans : program});
                newPrograms.push(program);
            }
        }
    }

    return newPrograms;
}

function bottomUpFaster(globalBnd, intOps, boolOps, vars, consts, inputoutput){
    
    writeToConsole("NYI");
}


function run1a1(){
    
    var rv = bottomUp(3, [VR, NUM, PLUS, TIMES, ITE], [AND, NOT, LT, FALSE], ["x", "y"], [4, 5], [{x:5,y:10, _out:5},{x:8,y:3, _out:3}]);
    writeToConsole("RESULT: " + rv.toString());
    
}


function run1a2(){
    
    var rv = bottomUp(3, [VR, NUM, PLUS, TIMES, ITE], [AND, NOT, LT, FALSE], ["x", "y"], [-1, 5], [
        {x:10, y:7, _out:17},
        {x:4, y:7, _out:-7},
        {x:10, y:3, _out:13},
        {x:1, y:-7, _out:-6},
        {x:1, y:8, _out:-8}     
        ]);
    writeToConsole("RESULT: " + rv.toString());
    
}


function run1b(){
    
    var rv = bottomUpFaster(3, [VR, NUM, PLUS, TIMES, ITE], [AND, NOT, LT, FALSE], ["x", "y"], [-1, 5], [
        {x:10, y:7, _out:17},
        {x:4, y:7, _out:-7},
        {x:10, y:3, _out:13},
        {x:1, y:-7, _out:-6},
        {x:1, y:8, _out:-8}     
        ]);
    writeToConsole("RESULT: " + rv.toString());
    
}


//Useful functions for exercise 2. 
//Not so much starter code, though.

function structured(inputoutputs){
    return "NYI";
}


function run2() {
    var inpt = JSON.parse(document.getElementById("input2").value);
    //This is the data from which you will synthesize.
    writeToConsole("You need to implement this");    
}


function genData() {
    //If you write a block of code in program1 that writes its output to a variable out,
    //and reads from variable x, this function will feed random inputs to that block of code
    //and write the input/output pairs to input2.
    program = document.getElementById("program1").value
    function gd(x) {
        var out;
        eval(program);
        return out;
    }
    textToIn = document.getElementById("input2");
    textToIn.value = "[";
    for(i=0; i<10; ++i){
        if(i!=0){ textToIn.textContent += ", "; }
        var inpt = randInt(0, 100);
        textToIn.value += "[" + inpt + ", " + gd(inpt) + "]";
    }
    textToIn.value += "]";
}