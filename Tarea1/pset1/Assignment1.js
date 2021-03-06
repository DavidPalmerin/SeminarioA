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

var ALLOPS  = [NUM, FALSE, VR, PLUS, TIMES, LT, AND, NOT, ITE];
var INTOPS  = [NUM, VR, PLUS, TIMES, ITE];
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
    var intPrograms = [];
    var boolPrograms = [flse()];
    vars.forEach(function(v) { intPrograms.push(vr(v)); });
    consts.forEach(function(v) { intPrograms.push(num(v)); });
    terminals = intPrograms;

    while (globalBnd > 0) {
        intPermutations = getParamsIndices(intPrograms.length);
        boolPermutations = getParamsIndices(boolPrograms.length);
        intPermutations[3] = getParamsIndicesIte(boolPermutations[1], intPermutations[2]);

        intsGrowth  = grow(intPrograms, boolPrograms, intPermutations, boolPermutations, intOps);
        boolsGrowth = grow(intPrograms, boolPrograms, intPermutations, boolPermutations, boolOps);
       
        intPrograms  = terminals.concat(elimEquivalents(intsGrowth, inputoutputs));
        boolPrograms = [flse()].concat(elimEquivalents(boolsGrowth, inputoutputs));

        var union = intPrograms.concat(boolPrograms);
        for (var i = 0; i < union.length; i++){
            if (isCorrect(union[i], inputoutputs)) {
                return union[i];
            }
        }
        globalBnd--;
    }
    return "FAIL";   
}



// ----------------------- IMPLEMENTATION OF 1.A ----------------------------------

function grow(intPrograms, boolPrograms, intPermutations, boolPermutations, ops) {
    var newPrograms = [];
    esBool = ops[0] == FALSE || ops[0] == NOT || ops[0] == LT || ops[0] == AND;
    for(var i = 0; i < ops.length; i++) {
        op = ops[i];
        synth_programs = undefined;
        if (!esBool || op == LT) 
            synth_programs = genPrograms(op, intPermutations, [intPrograms, boolPrograms]);
        else
            synth_programs = genPrograms(op, boolPermutations, [boolPrograms]);
        synth_programs.forEach(function(p){
            newPrograms.push(p);
        });
    }
    return newPrograms;
}

function genPrograms(op, permutations, arguments){
    var synth_programs = [];
    args = arguments[0];
    if (args.length == 0)
        return synth_programs;

    arity = operator_arity(op);
    arity_permutations = permutations[arity];
    if (arity > 0) {
        for(var i = 0; i < arity_permutations.length; i++) {
            args_indices = arity_permutations[i];
            var params = [];
            if (op == ITE && arguments[1].length > 0){
                boolArg = arguments[1][args_indices[0]];  // arguments[1] is the list of boolPrograms.
                args_indices.shift();
                params = args_indices.map(function(i){ return args[i]; });
                params.unshift(boolArg);
            }
            else if (op != ITE) 
                params = args_indices.map(function(i) { return args[i]; });
            
            myProgram = createNewProgram(op, params);
            if (!(myProgram === undefined))
                synth_programs.push(myProgram);
        }
    }
    return synth_programs;
}

function elimEquivalents(programs, inputoutputs) {
    var observationalTable = {};
    var programs_classes = [];
    for(var i = 0; i < programs.length; i++) {
        program = programs[i];
        for(var j = 0; j < inputoutputs.length; j++) {
            envt = inputoutputs[j];
            ans  = undefined;
            if (program.type == ITE)
                ans = [program.cond.toString(), interpret(program.tcase, envt).toString(), interpret(program.fcase, envt).toString()].toString();  
            else {
                if (program.type == FALSE || program.type == AND || program.type == NOT || program.type == LT)
                    ans = program.toString();
                else ans = interpret(program, envt);
            }
            
            if (!(ans in observationalTable)) {
                observationalTable[ans] = program;
                programs_classes.push(program);
            }
            // else console.log("Ya existe la clase de este programa: " + program.toString());
        }
    }
    return programs_classes;
}

function getParamsIndicesIte(boolPermutations, intPermutations){
    var indices = [];
    if (boolPermutations == undefined || intPermutations == undefined)
        return indices;

    for (var j = 0; j < intPermutations.length; j++) {
        casesArg = intPermutations[j];
        for (var i = 0; i < boolPermutations.length; i++) {
            boolArg = boolPermutations[i];
            permutation = [boolArg].concat(casesArg);
            indices.push(permutation);
        }
    }
    return indices;
}

function getParamsIndices(limit) {
    var indices = {};
    for(var i = 0; i < limit; i++) {
        if (1 in indices) 
            indices[1].push([i]);           
        else indices[1] = [[i]]; 
        for(var j = 0; j < limit; j++) {
            if (2 in indices) 
                indices[2].push([i, j]);
            else indices[2] = [[i, j]];
        }
    }

    return indices;
}   

function isCorrect(program, inputoutputs) {
    for (var i = 0; i < inputoutputs.length; i++) {
        current_input = inputoutputs[i];
        ans = interpret(program, current_input);
        if (ans != current_input['_out'])
            return false;
    }
    return true;
}

function createNewProgram(op, params) {
    switch(op) {
        case PLUS:
            return plus(params[0], params[1]);
            break;
        case TIMES:
            return times(params[0], params[1]);
            break;
        case LT:
            return lt(params[0], params[1]);
            break;
        case AND:
            return and(params[0], params[1]);
            break;
        case NOT:
            return not(params[0]);
            break;
        case ITE:
            return ite(params[0], params[1], params[2]);
            break;
        case NUM:
            if (typeof params[0] == typeof(0))
                return num(params[0]);
            break;
        case VR:
            if (typeof params[0] == typeof(" "))
                return vr(params[0]);
            break;
        case FALSE:
            return flse();
    }
    return undefined;
}

function operator_arity(op) {
    if (op == FALSE) return 0;
    if (op == VR || op == NUM || op == NOT) return 1;
    if (op == ITE) return 3;
    return 2;
}
// --------------------- END OF 1.A ---------------------------


function bottomUpFaster(globalBnd, intOps, boolOps, vars, consts, inputoutputs){
    var intPrograms = [];
    var boolPrograms = [flse()];
    vars.forEach(function(v) { intPrograms.push(vr(v)); });
    consts.forEach(function(v) { intPrograms.push(num(v)); });
    terminals = intPrograms;

    while (globalBnd > 0) {
        intPermutations = getParamsIndices(intPrograms.length);
        boolPermutations = getParamsIndices(boolPrograms.length);
        intPermutations[3] = getParamsIndicesIte(boolPermutations[1], intPermutations[2]);

        boolsGrowth = growFaster(intPrograms, boolPrograms, intPermutations, boolPermutations, boolOps);
        intsGrowth  = growFaster(intPrograms, boolPrograms, intPermutations, boolPermutations, intOps);
       
        intPrograms  = terminals.concat(elimEquivalents(intsGrowth, inputoutputs));
        boolPrograms = [flse()].concat(elimEquivalents(boolsGrowth, inputoutputs));

        var union = intPrograms.concat(boolPrograms);
        for (var i = 0; i < union.length; i++){
            if (isCorrect(union[i], inputoutputs)) {
                return union[i];
            }
        }
        globalBnd--;
        console.log(globalBnd);
    }

    writeToConsole("salio");
    return "FAIL";   
}

function growFaster(intPrograms, boolPrograms, intPermutations, boolPermutations, ops) {
    var newPrograms = [];
    esBool = ops[0] == FALSE || ops[0] == NOT || ops[0] == LT || ops[0] == AND;
    for(var i = 0; i < ops.length; i++) {
        op = ops[i];
        synth_programs = undefined;
        if (!esBool || op == LT) 
            synth_programs = genProgramsFaster(op, intPermutations, [intPrograms, boolPrograms]);
        else
            synth_programs = genProgramsFaster(op, boolPermutations, [boolPrograms]);
        synth_programs.forEach(function(p){
            newPrograms.push(p);
        });
    }
    return newPrograms;
}

function genProgramsFaster(op, permutations, arguments){
    var synth_programs = []
    args = arguments[0];
    if (args.length == 0)
        return synth_programs;

    arity = operator_arity(op);
    arity_permutations = permutations[arity];
    if (arity > 0) {
        for(var i = 0; i < arity_permutations.length; i++) {
            args_indices = arity_permutations[i];
            var params = [];
            if (op == ITE && arguments[1].length > 0){
                boolArg = arguments[1][args_indices[0]];  // arguments[1] is the list of boolPrograms.
                args_indices.shift();
                params = args_indices.map(function(i){ return args[i]; });
                params.unshift(boolArg);
            }
            else if (op != ITE) 
                params = args_indices.map(function(i) { return args[i]; });
            
            myProgram = createNewProgramFaster(op, params);
            if (!(myProgram === undefined)){
                synth_programs.push(myProgram);
            }
        }
    }
    return synth_programs;
}

function validTypes(type, validTypes){
    for(var i = 0; i < validTypes.length; i++){
        if(type == validTypes[i])
            return true;
    }
    return false;
}

function createNewProgramFaster(op, params) {
    switch(op) {
        case PLUS:
            return plus(params[0], params[1]);
            break;
        case TIMES:
            if (validTypes(params[0].type, [VR, NUM]) && validTypes(params[1].type, [VR, NUM]))               //Restricción de parametros válidos.
                return times(params[0], params[1]);
            break;
        case LT:
            if (validTypes(params[0].type, [VR, NUM]) && validTypes(params[1].type, [VR, NUM]))               //Restricción de parámetros válidos.
                return lt(params[0], params[1]);
            break;
        case AND:
            return and(params[0], params[1]);
            break;
        case NOT:
            return not(params[0]);
            break;
        case ITE:
            return ite(params[0], params[1], params[2]);
            break;
        case NUM:
            if (typeof params[0] == typeof(0))
                return num(params[0]);
            break;
        case VR:
            if (typeof params[0] == typeof(" "))
                return vr(params[0]);
            break;
        case FALSE:
            return flse();
    }
    return undefined;
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
	var rv = bottomUpFaster(2, [VR, NUM, PLUS, TIMES, ITE], [AND, NOT, LT, FALSE], ["x", "y"], [-1, 5], [
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

// term := 2*x + ?? | x*x + ?? | 3*x + ??
function structured(inputoutputs){
    ranges = {}
    const functions = [times(num(2), vr('x')),
                       times(vr('x'), vr('x')),
                       times(num(3), vr('x'))];
    
    const missed_consts = [function(_in, _out) { return _out - (2 * _in) },
                           function(_in, _out) { return _out - (_in * _in) },
                           function(_in, _out) { return _out - (3 *_in) } ];
    
    constsCounters = groupConstantsByFunctions(missed_consts, inputoutputs);   // Obtiene 3 diccionarios para las evaluaciones de las constantes ?? de cada función.

    index = 0;
    seen = {};
    while(index < 3) {
        group = constsCounters[index];
        keys = Object.keys(group);
        [lb, ub, max, key, fun, _in] = [-1, -1, -1, -1, -1];
        for (var j = 0; j < keys.length; j++) {                                // Obtiene el valor counter máximo en el j-ésimo diccionario correspondiente a missed_consts[j];
            [x, y, counter, k_in] = group[keys[j]];                            // Esto nos toma O(n) pues a lo más hay n llaves, pues cad auna corresponde a un input.
            if (counter > max)  
                [lb, ub, max, key, fun, _in] = [x, y, counter, keys[j], index, k_in];
        }
        if (max > 1) {
            constsCounters[index][key] = [-1, -1, -1, -1, -1, -1];
            if (!(_in in seen))                                                // Guarda tal valor máximo en caso de que no se haya guardado otro valor para el mismo input.
                seen[_in] = [lb, ub, max, parseInt(key), index, _in];   
        }
        else index++;
    }


    ranges = Object.values(seen);

    return buildExpression(ranges, functions);
}

// Función recursiva para construir el programa a partir de las reestricciones en expr.
// Expr es una lista de lista con restricciones de cada subprograma.
function buildExpression(exprs, functions) {
    if (exprs.length == 1) {
        [lb, ub, max, constant, exp_index] = exprs[0];
        return plus(functions[exp_index],constant);
    }
    [lb, ub, max, constant, exp_index] = exprs[0];  
    return ite(lt(vr('x'), num(ub + 1)), plus(functions[exp_index], constant), buildExpression(exprs.slice(1, exprs.length), functions));
}

// Crea un diccionario para cada función, donde se evalúa la función con los inputs.
// Cada llave es el resultado de despejar ?? en los terminos.
// El valor será una lista con un contador de las entradas que resultan tener la misma constante despejada.
// El valor mas imprtante en este momento es el contador, pues lo usaremos después, y además mantener actualizadas
// las cotas superiores e inferiores (lb, ub).
// Regresa un arreglo de tamaño 3, cada elemento es un diccionario correspondiente a cada función en functions.
// Toma 3 * O(n) pues la longitud de functions es 3.
// Gracias a que cada output pertenece a un único rango por HINT, sabemos que no contaremos mas de una vez en los contadores generados de cada 
// diccionario.
function groupConstantsByFunctions(functions, inputoutputs) {
    constsCounters = [{}, {}, {}];
    for (var i = 0; i < functions.length; i++) {
        f = functions[i];
        for (var j = 0; j < inputoutputs.length; j++) {
            const [_in, _out] = inputoutputs[j];
            ans = f(_in, _out);
            if (ans in constsCounters[i]) {
                [lb, ub, counter] = constsCounters[i][ans];
                newLb = lb < _in ? lb : _in;
                newUb = ub > _in ? ub : _in;
                constsCounters[i][ans] = [newLb, newUb, counter + 1, _in];
            }
            else constsCounters[i][ans] = [_in, _in, 1, _in];
        }
    } 

    return constsCounters;
}


function run2() {
    var input = JSON.parse(document.getElementById("input2").value);
    //This is the data from which you will synthesize.
    program = structured(input);
    writeToConsole("RESULT: " + program.toString());    
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
        textToIn.value += i < 9 ? "[" + inpt + ", " + gd(inpt) + "]," : "[" + inpt + ", " + gd(inpt) + "]";
    }
    textToIn.value += "]";
}
