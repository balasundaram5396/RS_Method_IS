//defining helper functions

//defining deep copy method
Array.prototype.copyDeep = function () {
  var result = [];
  for (var i = 0; i < this.length; i++) {
    if (this[i].isArray) result[i] = this[i].copyDeep();
    else result[i] = this[i];
  }
  return result;
};

Array.prototype.isArray = true;
// defining pop method
Array.prototype.remove = function (e) {
  var x = this.indexOf(e);
  if (x > -1) this.splice(x, 1);
};

//defining toString method for string conversion
Array.prototype.toString = function () {
  return '[' + this.join(',') + ']';
};

if (!Array.prototype.includes) {
  Array.prototype.includes = function (e) {
    for (var i = 0; i < this.length; i++) {
      if (this[i] == e) return true;
    }
    return false;
  };
}

// defining intersect method to find a element is present in the array
Array.prototype.intersect = function (e) {
  for (var i = 0; i < this.length; i++) {
    if (e.indexOf(this[i]) == -1) {
      this.splice(i--, 1);
    }
  }
};

//defining push function
Array.prototype.insert = function (e, x) {
  return this.splice(x, 0, e);
};

//defining getter method
Array.getArrayOfNumbers = function (length) {
  for (var i = 0, a = new Array(length); i < length; i++) a[i] = i;
  return a;
};

Array.prototype.concatNoDuplicates = function (array1) {
  var h1 = {};
  var r1 = [];
  for (var i = 0; i < this.length; i++) {
    h1[this[i].toString()] = true;
    r1.push(this[i]);
  }
  for (var i = 0; i < array1.length; i++) {
    var s = array1[i].toString();
    if (!h1[s]) {
      h1[s] = true;
      r1.push(array1[i]);
    }
  }
  return r1;
};

Array.prototype.equals = function (list) {
  if (this.length != list.length) return false;
  for (var i = 0; i < this.length; i++) {
    if (this[i].isArray) {
      if (!list[i].isArray) {
        return false;
      }
      if (!this[i].equals(list[i])) {
        return false;
      }
    } else if (this[i] != list[i]) {
      return false;
    }
  }
  return true;
};
// method to remove duplicates
Array.prototype.removeDuplicates = function () {
  var new1 = {};
  var old = [];
  for (var i = 0; i < this.length; i++) {
    var temp = this[i].toString();
    if (!new1[temp]) {
      new1[temp] = true;
      old.push(this[i]);
    }
  }
  return old;
};

Array.getArrayOfZeroes = function (length) {
  for (var i = 0, a = new Array(length); i < length; ) a[i++] = 0;
  return a;
};
// method to copy the values to a new array
Array.prototype.copy = function () {
  var result = [];
  for (var i = 0; i < this.length; i++) result[i] = this[i];
  return result;
};

function Formula() {}
Formula.prototype.toString = function () {
  return this.string;
};
Formula.prototype.equals = function (formula) {
  return this.string == formula.string;
};
Formula.prototype.negate = function () {
  return new NegatedFormula(this);
};
Formula.prototype.unify = function (formula) {
  var res = [];
  var i1, i2;
  if (this.predicate != formula.predicate) {
    return false;
  }
  if (this.type != 'literal') {
    return false;
  }
  if (this.terms.length != formula.terms.length) {
    return false;
  }
  if (this.sub && !formula.sub) {
    return false;
  }
  if (this.sub) {
    return this.sub.unify(formula.sub);
  }

  var val1 = this.terms.copyDeep();
  var val2 = formula.terms.copyDeep();

  while (((i1 = val1.shift()), (i2 = val2.shift()))) {
    log('unify terms? ' + i1 + ' <=> ' + i2);
    if (i1 == i2) {
      continue;
    }
    if (i1.isArray && i2.isArray) {
      if (i1[0] != i2[0]) return false;
      for (var i = 1; i < i1.length; i++) {
        val1.push(i1[i]);
        val2.push(i2[i]);
      }
      continue;
    }
    var i10 = i1[0] == 'ξ' || i1[0] == 'ζ';
    var i20 = i2[0] == 'ξ' || i2[0] == 'ζ';
    if (!i10 && !i20) {
      log('no, neither term variable');
      return false;
    }
    if (!i10) {
      var temp = i1;
      i1 = i2;
      i2 = temp;
    }
    if (i2.isArray) {
      var terms,
        termss = [i2];
      while ((terms = termss.shift())) {
        for (var i = 0; i < terms.length; i++) {
          if (terms[i].isArray) termss.push(terms[i]);
          else if (terms[i] == i1) return false;
        }
      }
    }
    log('yes: unify');
    var terms,
      termss = [res, val1, val2];
    while ((terms = termss.shift())) {
      for (var i = 0; i < terms.length; i++) {
        if (terms[i].isArray) termss.push(terms[i]);
        else if (terms[i] == i1) terms[i] = i2;
      }
    }
    res.push(i1);
    res.push(i2);
  }
  return res;
};
Formula.prototype.normalize = function () {
  var op = this.operator || this.quantifier;
  if (!op) return this;
  switch (op) {
    case '∧':
    case '∨': {
      var sub1 = this.sub1.normalize();
      var sub2 = this.sub2.normalize();
      return new BinaryFormula(op, sub1, sub2);
    }
    case '→': {
      var sub1 = this.sub1.negate().normalize();
      var sub2 = this.sub2.normalize();
      return new BinaryFormula('∨', sub1, sub2);
    }
    case '↔': {
      var sub1 = new BinaryFormula('∧', this.sub1, this.sub2).normalize();
      var sub2 = new BinaryFormula(
        '∧',
        this.sub1.negate(),
        this.sub2.negate()
      ).normalize();
      return new BinaryFormula('∨', sub1, sub2);
    }
    case '∀':
    case '∃': {
      return new QuantifiedFormula(
        op,
        this.variable,
        this.matrix.normalize(),
        this.overWorlds
      );
    }
    case '□':
    case '◇': {
      return new ModalFormula(op, this.sub.normalize());
    }
    case '¬': {
      var op2 = this.sub.operator || this.sub.quantifier;
      if (!op2) return this;
      switch (op2) {
        case '∧':
        case '∨': {
          var sub1 = this.sub.sub1.negate().normalize();
          var sub2 = this.sub.sub2.negate().normalize();
          var newOp = op2 == '∧' ? '∨' : '∧';
          return new BinaryFormula(newOp, sub1, sub2);
        }
        case '→': {
          var sub1 = this.sub.sub1.normalize();
          var sub2 = this.sub.sub2.negate().normalize();
          return new BinaryFormula('∧', sub1, sub2);
        }
        case '↔': {
          var sub1 = new BinaryFormula(
            '∧',
            this.sub.sub1,
            this.sub.sub2.negate()
          ).normalize();
          var sub2 = new BinaryFormula(
            '∧',
            this.sub.sub1.negate(),
            this.sub.sub2
          ).normalize();
          return new BinaryFormula('∨', sub1, sub2);
        }
        case '∀':
        case '∃': {
          var sub = this.sub.matrix.negate().normalize();
          return new QuantifiedFormula(
            op2 == '∀' ? '∃' : '∀',
            this.sub.variable,
            sub,
            this.sub.overWorlds
          );
        }
        case '□':
        case '◇': {
          var sub = this.sub.sub.negate().normalize();
          return new ModalFormula(op2 == '□' ? '◇' : '□', sub);
        }
        case '¬': {
          return this.sub.sub.normalize();
        }
      }
    }
  }
};
Formula.prototype.removeQuantifiers = function () {
  if (this.matrix) return this.matrix.removeQuantifiers();
  if (this.sub1) {
    var ns11 = this.sub1.quantifier
      ? this.sub1.matrix.removeQuantifiers()
      : this.sub1.removeQuantifiers();
    var ns12 = this.sub2.quantifier
      ? this.sub2.matrix.removeQuantifiers()
      : this.sub2.removeQuantifiers();
    if (this.sub1 == ns11 && this.sub2 == ns12) return this;
    var r1 = new BinaryFormula(this.operator, ns11, ns12);
    return r1;
  }
  return this;
};
Formula.prototype.alpha = function (n) {
  if (this.operator == '∧') {
    return n == 1 ? this.sub1 : this.sub2;
  }
  if (this.sub.operator == '∨') {
    return n == 1 ? this.sub.sub1.negate() : this.sub.sub2.negate();
  }
  if (this.sub.operator == '→') {
    return n == 1 ? this.sub.sub1 : this.sub.sub2.negate();
  }
};
Formula.prototype.beta = function (n) {
  if (this.operator == '∨') {
    return n == 1 ? this.sub1 : this.sub2;
  }
  if (this.operator == '→') {
    return n == 1 ? this.sub1.negate() : this.sub2;
  }
  if (this.operator == '↔') {
    return n == 1
      ? new BinaryFormula('∧', this.sub1, this.sub2)
      : new BinaryFormula('∧', this.sub1.negate(), this.sub2.negate());
  }
  if (this.sub.operator == '∧') {
    return n == 1 ? this.sub.sub1.negate() : this.sub.sub2.negate();
  }
  if (this.sub.operator == '↔') {
    return n == 1
      ? new BinaryFormula('∧', this.sub.sub1, this.sub.sub2.negate())
      : new BinaryFormula('∧', this.sub.sub1.negate(), this.sub.sub2);
  }
};
function AtomicFormula(predicate, terms) {
  this.type = 'literal';
  this.terms = terms;
  this.predicate = predicate;
  this.string = predicate + AtomicFormula.items2string(terms);
}
AtomicFormula.items2string = function (list) {
  var r1 = '';
  for (var i = 0; i < list.length; i++) {
    if (list[i].isArray) {
      var slist = list[i].copy();
      var fs = slist.shift();
      r1 += fs + '(' + AtomicFormula.items2string(slist) + ')';
    } else r1 += list[i];
  }
  return r1;
};
AtomicFormula.prototype = Object.create(Formula.prototype);
AtomicFormula.prototype.substitute = function (origTerm, newTerm, shallow) {
  if (typeof origTerm == 'string' && this.string.indexOf(origTerm) == -1) {
    return this;
  }
  var newitems = AtomicFormula.substituteInTerms(
    this.terms,
    origTerm,
    newTerm,
    shallow
  );
  if (!this.terms.equals(newitems)) {
    return new AtomicFormula(this.predicate, newitems);
  } else return this;
};
AtomicFormula.substituteInTerms = function (terms, origTerm, newTerm, shallow) {
  var newitems = [];
  for (var i = 0; i < terms.length; i++) {
    var term = terms[i];
    if (term == origTerm) newitems.push(newTerm);
    else if (term.isArray && !shallow) {
      newitems.push(AtomicFormula.substituteInTerms(term, origTerm, newTerm));
    } else newitems.push(term);
  }
  return newitems;
};
AtomicFormula.substituteInTerm = function (term, origTerm, newTerm) {
  if (term == origTerm) return newTerm;
  if (term.isArray)
    return AtomicFormula.substituteInTerms(term, origTerm, newTerm);
  return term;
};
function QuantifiedFormula(quantifier, variable, matrix, overWorlds) {
  this.quantifier = quantifier;
  this.matrix = matrix;
  this.overWorlds = overWorlds;
  this.variable = variable;
  if (overWorlds) {
    this.type = quantifier == '∀' ? 'modalGamma' : 'modalDelta';
  } else {
    this.type = quantifier == '∀' ? 'gamma' : 'delta';
  }
  this.string = quantifier + variable + matrix;
}
QuantifiedFormula.prototype = Object.create(Formula.prototype);
QuantifiedFormula.prototype.substitute = function (origTerm, newTerm, shallow) {
  if (this.variable == origTerm) return this;
  var nmat = this.matrix.substitute(origTerm, newTerm, shallow);
  if (nmat == this.matrix) return this;
  return new QuantifiedFormula(
    this.quantifier,
    this.variable,
    nmat,
    this.overWorlds
  );
};
function BinaryFormula(operator, sub1, sub2) {
  this.operator = operator;
  this.sub1 = sub1;
  this.sub2 = sub2;
  this.type = operator == '∧' ? 'alpha' : 'beta';
  this.string = '(' + sub1 + operator + sub2 + ')';
}
BinaryFormula.prototype = Object.create(Formula.prototype);
BinaryFormula.prototype.substitute = function (origTerm, newTerm, shallow) {
  var ns11 = this.sub1.substitute(origTerm, newTerm, shallow);
  var ns12 = this.sub2.substitute(origTerm, newTerm, shallow);
  if (this.sub1 == ns11 && this.sub2 == ns12) return this;
  return new BinaryFormula(this.operator, ns11, ns12);
};
function ModalFormula(operator, sub) {
  this.operator = operator;
  this.sub = sub;
  this.type = operator == '□' ? 'modalGamma' : 'modalDelta';
  this.string = operator + sub;
}
ModalFormula.prototype = Object.create(Formula.prototype);
ModalFormula.prototype.substitute = function (origTerm, newTerm, shallow) {
  var ns1 = this.sub.substitute(origTerm, newTerm, shallow);
  if (this.sub == ns1) return this;
  return new ModalFormula(this.operator, ns1);
};
function NegatedFormula(sub) {
  this.operator = '¬';
  this.sub = sub;
  this.type = NegatedFormula.computeType(sub);
  this.string = '¬' + sub;
}
NegatedFormula.computeType = function (sub) {
  if (sub.operator == '¬') return 'doublenegation';
  switch (sub.type) {
    case 'literal': {
      return 'literal';
    }
    case 'alpha': {
      return 'beta';
    }
    case 'beta': {
      return sub.operator == '↔' ? 'beta' : 'alpha';
    }
    case 'gamma': {
      return 'delta';
    }
    case 'delta': {
      return 'gamma';
    }
    case 'modalGamma': {
      return 'modalBeta';
    }
    case 'modalDelta': {
      return 'modalGamma';
    }
  }
};
NegatedFormula.prototype = Object.create(Formula.prototype);
NegatedFormula.prototype.substitute = function (origTerm, newTerm, shallow) {
  var ns1 = this.sub.substitute(origTerm, newTerm, shallow);
  if (this.sub == ns1) return this;
  return new NegatedFormula(ns1);
};
