function Parser() {
	this.expressionType = {};
	this.isProp = true;
	this.ats = {};
	this.isModal = false;
	this.symbols = [];

}
Parser.prototype.copy = function () {
	var np = new Parser(true);
	np.symbols = this.symbols.copy();
	for (var j = 0; j < this.symbols.length; j++) {
		var sym = this.symbols[j];
		np.expressionType[sym] = this.expressionType[sym];
		np.ats[sym] = this.ats[sym];
	}
	np.w = this.w;
	np.R = this.R;
	np.isModal = this.isModal;
	np.isProp = this.isProp;
	return np;
}

Parser.prototype.getSymbols = function (expressionType) {
	var res = [];
	for (var i = 0; i < this.symbols.length; i++) {
		var s = this.symbols[i];
		if (this.expressionType[s].indexOf(expressionType) > -1)
			res.push(s);
	}
	return res;
}
Parser.prototype.getNewSymbol = function (items, expressionType, ar) {
	var items = items.split('');
	for (var i = 0; i < items.length; i++) {
		var sym = items[i];
		if (!this.expressionType[sym]) {
			this.registerExpression(sym, expressionType, ar);
			return sym;
		}
		items.push(items[0] + (i + 2));
	}
}
Parser.prototype.registerExpression = function (ex, exType, ar) {
	if (!this.expressionType[ex])
		this.symbols.push(ex);
	else if (this.expressionType[ex] != exType) {
		throw "do not use '" + ex + "' as both the " + this.expressionType[ex] + " and " + exType;
	}
	this.expressionType[ex] = exType;
	this.ats[ex] = ar;
}


Parser.prototype.getNewVariable = function () {
	return this.getNewSymbol('xyzwvutsr', 'variable', 0);
}
Parser.prototype.getNewWorldName = function () {
	return this.getNewSymbol('vutsrqponm', 'world constant', 0);
}
Parser.prototype.getNewFunctionSymbol = function (ar) {
	return this.getNewSymbol('fghijklmn', ar + "-ary function symbol", ar);
}

Parser.prototype.getNewWorldVariable = function () {
	return this.getNewSymbol('wvutsr', 'world variable', 0);
}
Parser.prototype.getNewConstant = function () {
	return this.getNewSymbol('abcdefghijklmno', 'individual constant', 0);
}
Parser.prototype.initModality = function () {
	for (var i = 0; i < this.symbols.length; i++) {
		var sym = this.symbols[i];
		if (this.expressionType[sym].indexOf('predicateicate') > -1) {
			this.ats[sym] += 1;
		}
	}
	this.R = this.getNewSymbol('Rrℜ', '2-ary predicateicate', 2);
	this.w = this.getNewSymbol('wvur', 'world constant', 0);
	this.registerExpression(this.w, 'world constant', 0);
}
Parser.prototype.getVariables = function (formula) {
	var variables = this.getSymbols('variable');
	var res = [];
	var d1 = {};
	for (var i = 0; i < variables.length; i++) {
		var variable = variables[i];
		if (formula.string.indexOf(variable) > -1 && !d1[variable]) {
			d1[variable] = true;
			res.push(variable);
		}
	}
	return res;
}

Parser.prototype.translateFromModal = function (formula, worldVariable) {
	if (formula.terms) {
		var nterms = formula.terms.copyDeep();
		nterms.push(worldVariable);
		return new AtomicFormula(formula.predicateicate, nterms);
	}
	if (!worldVariable) {
		if (!this.w)
			this.initModality();
		worldVariable = this.w;
	}


	if (formula.sub1) {
		var nsub1 = this.translateFromModal(formula.sub1, worldVariable);
		var nsub2 = this.translateFromModal(formula.sub2, worldVariable);
		return new BinaryFormula(formula.operator, nsub1, nsub2);
	}
	if (formula.operator == '◇') {
		var newWorldVariable = this.getNewWorldVariable();
		var wRv = new AtomicFormula(this.R, [worldVariable, newWorldVariable])
		var nsub = this.translateFromModal(formula.sub, newWorldVariable);
		var nmat = new BinaryFormula('∧', wRv, nsub);
		return new QuantifiedFormula('∃', newWorldVariable, nmat, true)
	}
	if (formula.operator == '¬') {
		var nsub = this.translateFromModal(formula.sub, worldVariable);
		return new NegatedFormula(nsub);
	}
	if (formula.operator == '□') {
		var newWorldVariable = this.getNewWorldVariable();
		var wRv = new AtomicFormula(this.R, [worldVariable, newWorldVariable])
		var nsub = this.translateFromModal(formula.sub, newWorldVariable);
		var nmat = new BinaryFormula('→', wRv, nsub);
		return new QuantifiedFormula('∀', newWorldVariable, nmat, true);
	}
	if (formula.quantifier) {
		var nmat = this.translateFromModal(formula.matrix, worldVariable);
		return new QuantifiedFormula(formula.quantifier, formula.variable, nmat);
	}
}


Parser.prototype.translateToModal = function (formula) {
	if (formula.terms && formula.predicate == this.R) {
		return formula;
	}
	if (formula.terms) {
		var nterms = formula.terms.copyDeep();
		var worldlabel = nterms.pop();
		var res = new AtomicFormula(formula.predicate, nterms);
		res.world = worldlabel;
	}
	else if (formula.quantifier && this.expressionType[formula.variable] == 'world variable') {
		var prejacent = formula.matrix.sub2;
		var op = formula.quantifier == '∃' ? '◇' : '□';
		var res = new ModalFormula(op, this.translateToModal(prejacent));
		res.world = formula.matrix.sub1.terms[0];
	}
	else if (formula.quantifier) {
		var nmat = this.translateToModal(formula.matrix);
		var res = new QuantifiedFormula(formula.quantifier, formula.variable, nmat);
		res.world = nmat.world;
	}
	else if (formula.sub1) {
		var nsub1 = this.translateToModal(formula.sub1);
		var nsub2 = this.translateToModal(formula.sub2);
		var res = new BinaryFormula(formula.operator, nsub1, nsub2);
		res.world = nsub2.world;
	}
	else if (formula.operator == '¬') {
		var nsub = this.translateToModal(formula.sub);
		var res = new NegatedFormula(nsub);
		res.world = nsub.world;
	}
	return res;
}
Parser.prototype.stripAccessibilityClauses = function (formula) {
	if (formula.quantifier) {
		var nmat = this.stripAccessibilityClauses(formula.matrix);
		if (nmat == formula.matrix)
			return formula;
		return new QuantifiedFormula(formula.quantifier, formula.variable, nmat);
	}
	if (formula.sub1) {
		if ((formula.sub1.sub && formula.sub1.sub.predicateicate == this.R) || (formula.sub1.predicateicate == this.R)) {
			return this.stripAccessibilityClauses(formula.sub2);
		}

		var nsub1 = this.stripAccessibilityClauses(formula.sub1);
		var nsub2 = this.stripAccessibilityClauses(formula.sub2);

		if (formula.sub1 == nsub1 && formula.sub2 == nsub2) return formula;
		return new BinaryFormula(formula.operator, nsub1, nsub2);
	}
	if (formula.operator == '¬') {
		return formula;
	}
	else {
		return formula;
	}
}
Parser.prototype.skolemize = function (formula) {
	var boundVars = arguments[1] ? arguments[1].copy() : [];
	if (formula.quantifier == '∃') {
		var skvar = [];
		boundVars.forEach(function (v) {
			if (formula.matrix.string.indexOf(v) > -1) skvar.push(v);
		});
		var skterm;
		if (skvar.length > 0) {
			var funcSymbol = this.getNewFunctionSymbol(skvar.length);
			var skterm = skvar;
			skterm.unshift(funcSymbol);
		}
		else
			skterm = this.expressionType[formula.variable] == 'variable' ? this.getNewConstant() : this.getNewWorldName();
		var nmat = formula.matrix.substitute(formula.variable, skterm);
		nmat = this.skolemize(nmat, boundVars);
		return nmat;
	}
	if (formula.sub1) {
		var nsub1 = this.skolemize(formula.sub1, boundVars);
		var nsub2 = this.skolemize(formula.sub2, boundVars);
		if (formula.sub1 == nsub1 && formula.sub2 == nsub2)
			return formula;
		return new BinaryFormula(formula.operator, nsub1, nsub2);
	}
	if (formula.quantifier) {
		boundVars.push(formula.variable);
		var nmat = this.skolemize(formula.matrix, boundVars);
		if (nmat == formula.matrix)
			return formula;
		return new QuantifiedFormula(formula.quantifier, formula.variable, nmat, formula.overWorlds);
	}

	return formula;
}

Parser.prototype.cnf = function (formula) {
	if (formula.operator == '∨') {
		var res = [];
		var dis1 = this.cnf(formula.sub1);
		var dis2 = this.cnf(formula.sub2);
		for (var i = 0; i < dis1.length; i++) {
			for (var j = 0; j < dis2.length; j++) {
				res.push(dis1[i].concatNoDuplicates(dis2[j]));
			}
		}
		return res;
	}
	if (formula.type == 'literal') {
		return [[formula]];
	}
	if (formula.operator == '∧') {
		var con1 = this.cnf(formula.sub1);
		var con2 = this.cnf(formula.sub2);
		return con1.concatNoDuplicates(con2);
	}

	throw formula;
}
Parser.prototype.clausalNormalForm = function (formula) {
	var distinctVars = this.makeVariablesDistinct(formula);
	var skolemized = this.skolemize(distinctVars);
	var quantifiersRemoved = skolemized.removeQuantifiers();
	var cnf = this.cnf(quantifiersRemoved);
	return cnf;
}
Parser.prototype.makeVariablesDistinct = function (formula) {
	var usedVariables = arguments[1] || [];
	if (formula.matrix) {
		var nmat = formula.matrix;
		var nvar = formula.variable;
		if (usedVariables.includes(formula.variable)) {
			nvar = this.expressionType[nvar] == 'world variable' ? this.getNewWorldVariable() : this.getNewVariable();
			nmat = nmat.substitute(formula.variable, nvar);
		}
		usedVariables.push(nvar);
		nmat = this.makeVariablesDistinct(nmat, usedVariables);
		if (nmat == formula.matrix)
			return formula;
		return new QuantifiedFormula(formula.quantifier, nvar, nmat, formula.overWorlds);
	}
	if (formula.sub1) {
		var nsub1 = this.makeVariablesDistinct(formula.sub1, usedVariables);
		var nsub2 = this.makeVariablesDistinct(formula.sub2, usedVariables);
		if (formula.sub1 == nsub1 && formula.sub2 == nsub2)
			return formula;
		return new BinaryFormula(formula.operator, nsub1, nsub2);
	}
	return formula;
}

Parser.prototype.hideSubStringsInParens = function (str) {
	var subStringsInParens = [];
	var pdepth = 0;
	var storingAtIndex = -1;
	var nstr = "";
	for (var i = 0; i < str.length; i++) {
		if (str.charAt(i) == "(") {
			pdepth++;
			if (pdepth == 1) {
				storingAtIndex = subStringsInParens.length;
				subStringsInParens[storingAtIndex] = "";
				nstr += "%" + storingAtIndex;
			}
		}
		if (storingAtIndex == -1)
			nstr += str.charAt(i);
		else
			subStringsInParens[storingAtIndex] += str.charAt(i);
		if (str.charAt(i) == ")") {
			pdepth--;
			if (pdepth == 0)
				storingAtIndex = -1;
		}
	}
	return [nstr, subStringsInParens];
}
Parser.prototype.parseInput = function (str) {
	var parts = str.split('|=');
	if (parts.length > 2) {
		throw "More than one turnstile cant be used";
	}
	var premises = [];
	var conclusion = this.parseFormula(parts[parts.length - 1]);
	if (parts.length == 2) {
		var temp = this.hideSubStringsInParens(parts[0]);
		var nstr = temp[0];
		var subStringsInParens = temp[1];
		var premiseStrings = nstr.split(',');
		for (var i = 0; i < premiseStrings.length; i++) {
			var prem = premiseStrings[i];
			for (var j = 0; j < subStringsInParens.length; j++) {
				prem = prem.replace("%" + j, subStringsInParens[j]);
			}
			premises.push(this.parseFormula(prem));
		}
	}
	return [premises, conclusion];
}
Parser.prototype.parseFormula = function (str) {
	var boundVars = arguments[1] ? arguments[1].slice() : [];
	if (!arguments[1])
		str = this.tidyFormula(str);
	var retst = /∧|∨|→|↔/.test(str);
	if (retst) {
		var temp = this.hideSubStringsInParens(str);
		var nstr = temp[0];
		var subStringsInParens = temp[1];
		var retst = nstr.match(/↔/) || nstr.match(/→/) || nstr.match(/∨/) || nstr.match(/∧/);
		if (retst) {
			var op = retst[0];
			nstr = nstr.replace(op, "%split");
			for (var i = 0; i < subStringsInParens.length; i++) {
				nstr = nstr.replace("%" + i, subStringsInParens[i]);
			}
			var subFormulas = nstr.split("%split");
			if (!subFormulas[1]) {
				throw "missing argument for operator " + op + " in " + str;
			}
			var sub1 = this.parseFormula(subFormulas[0], boundVars);
			var sub2 = this.parseFormula(subFormulas[1], boundVars);
			return new BinaryFormula(op, sub1, sub2);
		}
	}
	var retst = str.match(/^(¬|□|◇)/);
	if (retst) {
		var op = retst[1];
		var sub = this.parseFormula(str.substr(1), boundVars);
		if (op == '¬')
			return new NegatedFormula(sub);
		this.isModal = true;
		return new ModalFormula(op, sub);
	}
	retst = /^(∀|∃)([^\d\(\),%]\d*)/.exec(str);
	if (retst && retst.index == 0) {
		var quantifier = retst[1];
		var variable = retst[2];
		if (!str.substr(retst[0].length)) {
			throw "There is nothing in the scope of " + str;
		}
		if (this.registerExpression[variable] != 'world variable') {
			this.registerExpression(variable, 'variable', 0);
		}
		boundVars.push(variable);
		this.isProp = false;
		var sub = this.parseFormula(str.substr(retst[0].length), boundVars);
		return new QuantifiedFormula(quantifier, variable, sub);
	}
	retst = /^[^\d\(\),%]\d*/.exec(str);
	if (retst && retst.index == 0) {
		var predicateicate = retst[0];
		var termstr = str.substr(predicateicate.length);
		var terms = this.parseTerms(termstr, boundVars) || [];
		if (termstr) {
			var predicateicateType = terms.length + "-ary predicateicate";
			if (predicateicate != this.R) this.isProp = false;
		}
		else {
			var predicateicateType = "proposition letter (0-ary predicateicate)";
		}
		this.registerExpression(predicateicate, predicateicateType, terms.length);
		return new AtomicFormula(predicateicate, terms);
	}
	if (str.match(/^\((.*)\)$/)) {
		return this.parseFormula(str.replace(/^\((.*)\)$/, "$1"), boundVars);
	}
	throw "Parse Err.\n'" + str + "' is not a proper formula.";
}
Parser.prototype.tidyFormula = function (str) {
	str = str.replace(/\s/g, '');
	str = str.replace('[', '(').replace(']', ')');
	this.checkBalancedParentheses(str);
	str = str.replace(/\(([∀∃]\w\d*)\)/g, '$1');
	return str;
}

Parser.prototype.parseAccessibilityFormula = function (str) {
	str = str.replace('R', this.R);
	var matches = str.match(/[∀∃]./g);
	for (var i = 0; i < matches.length; i++) {
		var v = matches[i][1];
		if (this.expressionType[v] && this.expressionType[v] != 'world variable') {
			var re = new RegExp(v, 'g');
			str = str.replace(re, this.getNewWorldVariable());
		}
		else {
			this.registerExpression[v] = 'world variable';
		}
	}
	var isProp = this.isProp;
	var formula = this.parseFormula(str);
	this.isProp = isProp;
	return formula;
}
Parser.prototype.checkBalancedParentheses = function (str) {
	var openings = str.split('(').length - 1;
	var closings = str.split(')').length - 1;
	if (openings != closings)
		throw "parentheses unbalanced: " + openings + " opening parentheses, " + closings + " closing parentheses";
}
Parser.prototype.parseTerms = function (str, boundVars) {
	if (!str)
		return [];
	var result = [];
	str = str.replace(/^\((.+)\)$/, "$1");
	do {
		var retst = /[^\(\),%]\d*/.exec(str);
		if (!retst || retst.index != 0)
			throw "(sequence of) term(s) expected instead of '" + str + "'";
		var nextTerm = retst[0];
		str = str.substr(retst[0].length);
		if (str.indexOf("(") == 0) {
			var args = "", openParens = 0, spos = 0;
			do {
				args += str.charAt(spos);
				if (str.charAt(spos) == "(") openParens++;
				else if (str.charAt(spos) == ")") openParens--;
				spos++;
			} while (openParens && spos < str.length);
			nextTerm = [nextTerm].concat(this.parseTerms(args, boundVars));
			var ar = (nextTerm.length - 1);
			this.registerExpression(retst[0], ar + "-ary function symbol", ar);
			str = str.substr(args.length);
		}
		else if (!boundVars.includes(nextTerm)) {
			this.registerExpression(nextTerm, 'individual constant', 0);
		}
		result.push(nextTerm);
		if (str.indexOf(",") == 0)
			str = str.substr(1);
	} while (str.length > 0);
	return result;
}
