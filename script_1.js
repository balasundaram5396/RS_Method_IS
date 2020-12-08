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

Array.prototype.concatNoDuplicates = function (arr) {
  var a = {};
  var b = [];
  for (var i = 0; i < this.length; i++) {
    a[this[i].toString()] = true;
    b.push(this[i]);
  }
  for (var i = 0; i < arr.length; i++) {
    var s = arr[i].toString();
    if (!a[s]) {
      a[s] = true;
      b.push(arr[i]);
    }
  }
  return b;
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
Formula.prototype.alpha = function (val) {
  if (this.operator == '∧') {
    return val == 1 ? this.sub1 : this.sub2;
  }
  if (this.sub.operator == '∨') {
    return val == 1 ? this.sub.sub1.negate() : this.sub.sub2.negate();
  }
  if (this.sub.operator == '→') {
    return val == 1 ? this.sub.sub1 : this.sub.sub2.negate();
  }
};
Formula.prototype.beta = function (val) {
  if (this.operator == '→') {
    return val == 1 ? this.sub1.negate() : this.sub2;
  }
  if (this.operator == '∨') {
    return val == 1 ? this.sub1 : this.sub2;
  }
  if (this.operator == '↔') {
    return val == 1
      ? new BinaryFormula('∧', this.sub1, this.sub2)
      : new BinaryFormula('∧', this.sub1.negate(), this.sub2.negate());
  }
  if (this.sub.operator == '∧') {
    return val == 1 ? this.sub.sub1.negate() : this.sub.sub2.negate();
  }
  if (this.sub.operator == '↔') {
    return val == 1
      ? new BinaryFormula('∧', this.sub.sub1, this.sub.sub2.negate())
      : new BinaryFormula('∧', this.sub.sub1.negate(), this.sub.sub2);
  }
};
Formula.prototype.toString = function () {
  return this.string;
};
Formula.prototype.equals = function (formula) {
  return this.string == formula.string;
};
Formula.prototype.negate = function () {
  return new NegatedFormula(this);
};
Formula.prototype.normalize = function () {
  var sym = this.operator || this.quantifier;
  if (!sym) return this;
  switch (sym) {
    case '∧':
    case '∨': {
      var sub1 = this.sub1.normalize();
      var sub2 = this.sub2.normalize();
      return new BinaryFormula(sym, sub1, sub2);
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
    case '→': {
      var sub1 = this.sub1.negate().normalize();
      var sub2 = this.sub2.normalize();
      return new BinaryFormula('∨', sub1, sub2);
    }
    case '□':
    case '◇': {
      return new ModalFormula(sym, this.sub.normalize());
    }
    case '¬': {
      var sym2 = this.sub.operator || this.sub.quantifier;
      if (!sym2) return this;
      switch (sym2) {
        case '∧':
        case '∨': {
          var sub1 = this.sub.sub1.negate().normalize();
          var sub2 = this.sub.sub2.negate().normalize();
          var newOp = sym2 == '∧' ? '∨' : '∧';
          return new BinaryFormula(newOp, sub1, sub2);
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
        case '→': {
          var sub1 = this.sub.sub1.normalize();
          var sub2 = this.sub.sub2.negate().normalize();
          return new BinaryFormula('∧', sub1, sub2);
        }

        case '□':
        case '◇': {
          var sub = this.sub.sub.negate().normalize();
          return new ModalFormula(sym2 == '□' ? '◇' : '□', sub);
        }
        case '¬': {
          return this.sub.sub.normalize();
        }
      }
    }
  }
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
    var ival = i1[0] == 'ξ' || i1[0] == 'ζ';
    var ival2 = i2[0] == 'ξ' || i2[0] == 'ζ';
    if (!ival && !ival2) {
      return false;
    }
    if (!ival) {
      var temp = i1;
      i1 = i2;
      i2 = temp;
    }
    if (i2.isArray) {
      var terms,
        term_val = [i2];
      while ((terms = term_val.shift())) {
        for (var i = 0; i < terms.length; i++) {
          if (terms[i].isArray) term_val.push(terms[i]);
          else if (terms[i] == i1) return false;
        }
      }
    }
    var terms,
      term_val = [res, val1, val2];
    while ((terms = term_val.shift())) {
      for (var i = 0; i < terms.length; i++) {
        if (terms[i].isArray) term_val.push(terms[i]);
        else if (terms[i] == i1) terms[i] = i2;
      }
    }
    res.push(i1);
    res.push(i2);
  }
  return res;
};

Formula.prototype.removeQuantifiers = function () {
  if (this.matrix) return this.matrix.removeQuantifiers();
  if (this.sub1) {
    var num1 = this.sub1.quantifier
      ? this.sub1.matrix.removeQuantifiers()
      : this.sub1.removeQuantifiers();
    var num2 = this.sub2.quantifier
      ? this.sub2.matrix.removeQuantifiers()
      : this.sub2.removeQuantifiers();
    if (this.sub1 == num1 && this.sub2 == num2) return this;
    var b = new BinaryFormula(this.operator, num1, num2);
    return b;
  }
  return this;
};

function ModalFormula(operator, sub) {
  this.operator = operator;
  this.type = operator == '□' ? 'modalGamma' : 'modalDelta';
  this.sub = sub;
  this.string = operator + sub;
}
ModalFormula.prototype = Object.create(Formula.prototype);
ModalFormula.prototype.substitute = function (origTerm, newTerm, shallow) {
  var n1 = this.sub.substitute(origTerm, newTerm, shallow);
  if (this.sub == n1) return this;
  return new ModalFormula(this.operator, n1);
};

function NegatedFormula(sub) {
  this.operator = '¬';
  this.sub = sub;
  this.type = NegatedFormula.computeType(sub);
  this.string = '¬' + sub;
}
NegatedFormula.prototype = Object.create(Formula.prototype);
NegatedFormula.prototype.substitute = function (origTerm, newTerm, shallow) {
  var n1 = this.sub.substitute(origTerm, newTerm, shallow);
  if (this.sub == n1) return this;
  return new NegatedFormula(n1);
};
NegatedFormula.computeType = function (sub) {
  if (sub.operator == '¬') return 'doublenegation';
  switch (sub.type) {
    case 'literal': {
      return 'literal';
    }
    case 'modalDelta': {
      return 'modalGamma';
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
  }
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
  var num1 = this.sub1.substitute(origTerm, newTerm, shallow);
  var num2 = this.sub2.substitute(origTerm, newTerm, shallow);
  if (this.sub1 == num1 && this.sub2 == num2) {
    return this;
  }
  return new BinaryFormula(this.operator, num1, num2);
};

function QuantifiedFormula(quantifier, variable, matrix, newVal) {
  this.quantifier = quantifier;
  this.matrix = matrix;
  this.newVal = newVal;
  this.variable = variable;
  if (newVal) {
    this.type = quantifier == '∀' ? 'modalGamma' : 'modalDelta';
  } else {
    this.type = quantifier == '∀' ? 'gamma' : 'delta';
  }
  this.string = quantifier + variable + matrix;
}
QuantifiedFormula.prototype = Object.create(Formula.prototype);
QuantifiedFormula.prototype.substitute = function (origTerm, newTerm, shallow) {
  if (this.variable == origTerm) return this;
  var n = this.matrix.substitute(origTerm, newTerm, shallow);
  if (n == this.matrix) return this;
  return new QuantifiedFormula(this.quantifier, this.variable, n, this.newVal);
};

function AtomicFormula(predicate, terms) {
  this.type = 'literal';
  this.terms = terms;
  this.predicate = predicate;
  this.string = predicate + AtomicFormula.items2string(terms);
}
AtomicFormula.prototype = Object.create(Formula.prototype);
AtomicFormula.items2string = function (list) {
  var r = '';
  for (var i = 0; i < list.length; i++) {
    if (list[i].isArray) {
      var newList = list[i].copy();
      var x = newList.shift();
      r += x + '(' + AtomicFormula.items2string(newList) + ')';
    } else r += list[i];
  }
  return r;
};
AtomicFormula.prototype.substitute = function (origTerm, newTerm, shallow) {
  if (typeof origTerm == 'string' && this.string.indexOf(origTerm) == -1) {
    return this;
  }
  var newIt = AtomicFormula.substituteInTerms(
    this.terms,
    origTerm,
    newTerm,
    shallow
  );
  if (!this.terms.equals(newIt)) {
    return new AtomicFormula(this.predicate, newIt);
  } else return this;
};
AtomicFormula.substituteInTerm = function (term, origTerm, newTerm) {
  if (term == origTerm) return newTerm;
  if (term.isArray)
    return AtomicFormula.substituteInTerms(term, origTerm, newTerm);
  return term;
};
AtomicFormula.substituteInTerms = function (terms, origTerm, newTerm, shallow) {
  var newIt = [];
  for (var i = 0; i < terms.length; i++) {
    var term = terms[i];
    if (term == origTerm) newIt.push(newTerm);
    else if (term.isArray && !shallow) {
      newIt.push(AtomicFormula.substituteInTerms(term, origTerm, newTerm));
    } else newIt.push(term);
  }
  return newIt;
};
