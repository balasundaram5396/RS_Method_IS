function STree(fvTree, parser) {
    this.nodes = [];
    this.isClosed = (fvTree.openBranches.length == 0);
    this.initFormulas = fvTree.prover.initFormulas;
    this.initFormulasNonModal = fvTree.prover.initFormulasNonModal;
    this.initFormulasNormalized = fvTree.prover.initFormulasNormalized;
    this.fvTree = fvTree;
    this.parser = parser; 
    this.parserFV = fvTree.parser; 
    this.markEndNodesClosed();
    this.changeNodes();
    this.removeUnusedNodes();
    this.replaceFreeVariablesAndSkolemTerms();
}

STree.prototype.transferNode = function(node, par) {
    var formula_node = node.formula;
    for (var i=0; i<node.fromNodes.length; i++) {
        if (node.fromNodes[i].formula.type == 'doublenegation') {
            this.expandDoubleNegation(node.fromNodes[i]);
            node.fromNodes[i] = node.fromNodes[i].doubleNegate;
        }
    }
    if (par.doubleNegate) par = par.doubleNegate;
        
    switch (node.fromRule) {

    case Prover.beta: {
        var from = node.fromNodes[0];
        var a1 = from.formula.beta(1);
        var a2 = from.formula.beta(2);
        if (!formula_node.equals(a1.normalize())) node.formula = a2;
        else if (!formula_node.equals(a2.normalize())) node.formula = a1;
        else {
            node.formula = (par.children && par.children.length) ? a2 : a1;
        }
        if (from.formula.operator == '↔' ||
            (from.formula.operator == '¬' && from.formula.sub.operator == '↔')) {
            node.biConditionFull = true;
            node.used = false;
        }
        this.appendChild(par, node);
        if (par.children.length == 2 && node.formula == a1) {
            par.children.reverse();
        }
        return node;
    }

    case Prover.alpha : {
        var from = node.fromNodes[0];
        var a1 = from.formula.alpha(1);
        var a2 = from.formula.alpha(2);
        if (from.biConditionFull) {
            node.fromNodes = from.fromNodes;
            node.expansionStep = from.expansionStep;
        }
        if (!formula_node.equals(a1.normalize())) node.formula = a2;
        else if (!formula_node.equals(a2.normalize())) node.formula = a1;
        else {
            node.formula = (par.fromNodes[0] && par.fromNodes[0] == from) ? a2 : a1;
        }
        this.appendChild(par, node);
        if (par.fromNodes[0] && par.fromNodes[0] == from && node.formula == a1) {
            this.reverse(par, node);
            return par;
        }
        else return node;
        
        
    }

    case Prover.modalGamma: {
        var from = node.fromNodes[0];
        if (from.formula.sub) {
            var newFla = from.formula.sub.matrix.sub2.negate();
            var boundVar = from.formula.sub.variable;
        }
        else { 
            var newFla = from.formula.matrix.sub2;
            var boundVar = from.formula.variable;
        }
        node.formula = newFla.substitute(boundVar, node.instanceTerm);
        this.appendChild(par, node);
        return node;
    }

    case Prover.gamma: case Prover.delta: {
        var from = node.fromNodes[0];
        var matrix = from.formula.matrix || from.formula.sub.matrix;
        if (this.fvTree.prover.s5 && matrix.sub1 &&
            matrix.sub1.predicate == this.parserFV.R) {
            var newFla = from.formula.sub ? matrix.sub2.negate() : matrix.sub2;
        }
        else {
            var newFla = from.formula.sub ? matrix.negate() : matrix;
        }
        var boundVar = from.formula.sub ? from.formula.sub.variable : from.formula.variable;
        if (node.instanceTerm) {
            node.formula = newFla.substitute(boundVar, node.instanceTerm);
        }
        else {
            node.formula = newFla;
        }
        this.appendChild(par, node);
        return node;
    }

    case Prover.modalDelta: 
        var from = node.fromNodes[0];
        if (node.formula.predicate == this.parserFV.R) {
            this.appendChild(par, node);
        }
        else {
            if (from.formula.sub) { 
                var newFla = from.formula.sub.matrix.sub2.negate();
                var boundVar = from.formula.sub.variable;
            }
            else {
                var newFla = from.formula.matrix.sub2;
                var boundVar = from.formula.variable;
            }
            node.formula = newFla.substitute(boundVar, node.instanceTerm);
            this.appendChild(par, node);
        }
        return node;
        
    default: {
        this.appendChild(par, node);
        return node;
    }
    }
}

STree.prototype.markEndNodesClosed = function() {
    for (var i=0; i<this.fvTree.closedBranches.length; i++) {
        var branch = this.fvTree.closedBranches[i]; 
        branch.nodes[branch.nodes.length-1].closedEnd = true;
    }
}

STree.prototype.changeNodes = function() {

    this.addInitNodes();
    var branches = this.fvTree.closedBranches.concat(this.fvTree.openBranches);
    for (var b=0; b<branches.length; b++) {
        var par;
        for (var n=0; n<branches[b].nodes.length; n++) {
            var node = branches[b].nodes[n];
            if (node.isSenNode) {
                par = node.swappedWith || node;
                continue;
            }
            par = this.transferNode(node, par);
        }
    }
}

STree.prototype.addInitNodes = function() {
    var branch = this.fvTree.closedBranches.length > 0 ?
        this.fvTree.closedBranches[0] : this.fvTree.openBranches[0];
    
    for (var i=0; i<this.initFormulasNonModal.length; i++) {
        var node = this.makeNode(branch.nodes[i]);
        node.formula = this.initFormulasNonModal[i];
        node.used = true; 
        if (i==0) this.nodes.push(node);
        else this.appendChild(this.nodes[i-1], node);
    }
}

STree.prototype.expandDoubleNegation = function(node) {
    if (node.doubleNegate) return;
    var newNode = new Node(node.formula.sub.sub, null, [node]);
    this.makeNode(newNode);
    node.doubleNegate = newNode;
    var dnePar = node;
    if (node.children[0] && node.children[0].fromNodes[0] == node.fromNodes[0]) {
        dnePar = node.children[0];
    }
    newNode.parent = dnePar;
    newNode.children = dnePar.children;
    dnePar.children = [newNode];
    for (var i=0; i<newNode.children.length; i++) {
        newNode.children[i].parent = newNode;
    }
    newNode.used = node.used;
    this.nodes.push(newNode);
} 

STree.prototype.replaceFreeVariablesAndSkolemTerms = function() {
    var meanings = {};
    for (var n=0; n<this.nodes.length; n++) {
        var node = this.nodes[n];
        var varMatches = node.formula.string.match(/[ξζ]\d+/g);
        if (varMatches) {
            for (var j=0; j<varMatches.length; j++) {
                var fv = varMatches[j];
                if (!meanings[fv]) {
                    var sym = (fv[0] == 'ζ') ?
                        this.parser.getNewWorldName() : this.parser.getNewConstant();
                    meanings[fv] = sym;
                }
                node.formula = node.formula.substitute(
                    fv, meanings[fv]
                );
            }
        }
        var skterms = getSkolemTerms(node.formula);
        var separateTerms = skterms[0], universalTerms = skterms[1];
        for (var c=0; c<separateTerms.length; c++) {
            var termstr = separateTerms[c].toString();
            if (!meanings[termstr]) {
                meanings[termstr] = this.parser.getNewConstant();
            }
            node.formula = node.formula.substitute(
                separateTerms[c], meanings[termstr]
            );
        }
        for (var c=0; c<universalTerms.length; c++) {
            var termstr = universalTerms[c].toString();
            if (!meanings[termstr]) {
                meanings[termstr] = this.parser.getNewWorldName(true);
            }
            node.formula = node.formula.substitute(
                universalTerms[c], meanings[termstr]
            );
        }
    }
    
    function getSkolemTerms(formula) {
        var universalTerms = [];
        var separateTerms = [];
        var flas = [formula]; 
        var fla;
        while ((fla = flas.shift())) {
            if (fla.isArray) { 
                for (var i=0; i<fla.length; i++) {
                    if (fla[i].isArray) {
                        if (fla[i][0][0] == 'φ') separateTerms.push(fla[i]);
                        else if (fla[i][0][0] == 'ω') universalTerms.push(fla[i]);
                        else flas.unshift(fla[i]);
                    }
                    else {
                        if (fla[i][0] == 'φ') separateTerms.push(fla[i]);
                        else if (fla[i][0] == 'ω') universalTerms.push(fla[i]);
                    }
                }
            }
            else if (fla.sub) {
                flas.unshift(fla.sub);
            }
            else if (fla.sub1) {
                flas.unshift(fla.sub1);
                flas.unshift(fla.sub2);
            }
            else if (fla.matrix) {
                flas.unshift(fla.matrix);
            }
            else {
                flas.unshift(fla.terms);
            }
        }
        return [separateTerms, universalTerms];
    }
}

STree.prototype.removeUnusedNodes = function() {
    if (!this.isClosed) return;
    for (var i=0; i<this.nodes.length; i++) {
        var node = this.nodes[i];
        if (node.used) {
            var expansion = this.getExpansion(node);
            for (var j=0; j<expansion.length; j++) {
                if (!expansion[j].biConditionFull) {
                    expansion[j].used = true;
                }
            }
        }
    }
    for (var i=0; i<this.nodes.length; i++) {
        if (!this.nodes[i].used) {
            var ok = this.remove(this.nodes[i]);
            if (ok) i--; 
        }
    }
}

STree.prototype.createModel = function() {
    for (var i=0; i<this.nodes.length; i++) {
        var node = this.nodes[i];
        node.formula = this.parserFV.translateToModal(node.formula);
        if (node.formula.predicate == this.parserFV.R) {
            node.formula.string = node.formula.terms[0] + this.parserFV.R
                + node.formula.terms[1];
        }
    }
}

STree.prototype.makeNode = function(node) {
    node.parent = null;
    node.children = [];
    node.isSenNode = true;
    return node;
}

STree.prototype.appendChild = function(oldNode, newNode) {
   if (!newNode.isSenNode) {
       newNode = this.makeNode(newNode);
   }
   newNode.parent = oldNode;
   oldNode.children.push(newNode);
   if (oldNode.closedEnd) {
      oldNode.closedEnd = false;
      newNode.closedEnd = true;
   }
   this.nodes.push(newNode);
   return newNode;
}

STree.prototype.remove = function(node) {
    if (node.isRemoved) return;
    if (node.parent.children.length == 1) {
        node.parent.children = node.children;
        if (node.children[0]) {
            node.children[0].parent = node.parent;
            node.children[0].instanceTerm = node.instanceTerm;
        }
        if (node.children[1]) {
            node.children[1].parent = node.parent;
            node.children[1].instanceTerm = node.instanceTerm;
        }
    }
    else {
        if (node.children.length > 1) {
            return false;
        }
        var i = (node == node.parent.children[0]) ? 0 : 1;
        if (node.children[0]) {
            node.parent.children[i] = node.children[0];
            node.children[0].parent = node.parent;
            node.children[0].instanceTerm = node.instanceTerm;
        }
        else node.parent.children.remove(node);
    }
    this.nodes.remove(node);
    node.isRemoved = true;
    return true;
}

STree.prototype.toString = function() {
   return "<table><tr><td align='center' style='font-family:monospace'>"+getTree(this.nodes[0])+"</td</tr></table>";
   function getTree(node) {
      var recursionDepth = arguments[1] || 0;
      if (++recursionDepth > 40) return "<b>...<br>[max recursion]</b>";
      var res = (node.used ? '.' : '') + node + (node.closedEnd ? "<br>x<br>" : "<br>");
      if (node.children[1]) res += "<table><tr><td align='center' valign='top' style='font-family:monospace; border-top:1px solid #999; padding:3px; border-right:1px solid #999'>" + getTree(node.children[0], recursionDepth) + "</td>\n<td align='center' valign='top' style='padding:3px; border-top:1px solid #999; font-family:monospace'>" + getTree(node.children[1], recursionDepth) + "</td>\n</tr></table>";
      else if (node.children[0]) res += getTree(node.children[0], recursionDepth);
      return res;
   }
}

STree.prototype.substitute = function(oldTerm, newTerm) {
    for (var i=0; i<this.nodes.length; i++) {
        this.nodes[i].formula = this.nodes[i].formula.substitute(oldTerm, newTerm);
    }
}

STree.prototype.reverse = function(node1, node2) {
   node2.parent = node1.parent;
   node1.parent = node2;
   if (node2.parent.children[0] == node1) node2.parent.children[0] = node2;
   else node2.parent.children[1] = node2;
   node1.children = node2.children;
   node2.children = [node1];
   if (node1.children[0]) node1.children[0].parent = node1;
   if (node1.children[1]) node1.children[1].parent = node1;
   if (node2.closedEnd) {
      node2.closedEnd = false;
      node1.closedEnd = true;
   }
   node2.swappedWith = node1;
   node1.swappedWith = node2;
}

STree.prototype.getExpansion = function(node) {
    
    var res = [node];

    if (!node.expansionStep) return res; 
    var par = node.parent;
    while (par && par.expansionStep == node.expansionStep) {
        res.unshift(par);
        par = par.parent;
    }
    
    var ch = node.children[0];
    while (ch && ch.expansionStep == node.expansionStep) {
        res.push(ch);
        ch = ch.children[0];
    }
    
    if (par) {
        for (var i=0; i<par.children.length; i++) {
            var sibling = par.children[i];
            while (sibling && sibling.expansionStep == node.expansionStep) {
                if (!res.includes(sibling)) res.push(sibling);
                sibling = sibling.children[0];
            }
        }
    }
    
    return res;
}

STree.prototype.getCountVal = function() {
    var endNode = null;
    for (var i=0; i<this.nodes.length; i++) {
        if (this.nodes[i].children.length || this.nodes[i].closedEnd) continue;
        endNode = this.nodes[i];
        break;
    }
    if (!endNode) return null;
    
    var model = new Model(this.fvTree.prover.modelfinder, 0, 0);
   
    var node = endNode;
    if (this.parser.isModal) {
        model.worlds = [0];
        model.interpretation['w'] = 0;
    }
    do {
        var fla = node.formula;
        while (fla.operator == '¬' && fla.sub.operator == '¬') {
            fla = fla.sub.sub;
        }
        var atom = (fla.operator == '¬') ? fla.sub : fla;
        if (!atom.predicate) continue;
        var terms = atom.terms.copy();
        for (var t=0; t<terms.length; t++) {
            if (terms[t].isArray) {
                for (var i=1; i<terms[t].length; i++) {
                    terms.push(terms[t][i]);
                }
            }
        }
        terms.sort(function(a,b) {
            return a.toString().length < b.toString().length;
        });
        for (var t=0; t<terms.length; t++) {
            var term = terms[t];
            var rterm = model.reduceArguments(terms[t]).toString();
            if (rterm in model.interpretation) continue;
            var domain = this.parserFV.expressionType[term] &&
                this.parserFV.expressionType[term].indexOf('world') > -1 ? 
                model.worlds : model.domain;
            domain.push(domain.length);
            model.interpretation[rterm] = domain.length-1;
        }
        if (!model.satisfy(fla)) {
            return null;
        }
    } while ((node = node.parent));
    
    if (model.domain.length == 0) {
        model.domain = [0];
    }
    return model;
}

