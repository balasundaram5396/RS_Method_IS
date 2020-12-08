function TPaint(sTree, rootAnchor) {
    this.paintInterval = 200;      
    this.branchPadding = window.innerWidth < 500 ? 0 :
        window.innerWidth < 800 ? 20 : 30;
    this.branchHeight = 40;    
    this.nodeHiParentCSS = "treeNodeHiParent" 
    this.nodeHiChildCSS = "treeNodeHiChild"  
    this.tree = sTree;
    this.isModal = sTree.parser.isModal;
    this.rootAnchor = rootAnchor;
    this.rootAnchor.innerHTML = "";
    this.minX = this.branchPadding/2 - rootAnchor.offsetLeft;
    this.scale = 1;
    this.currNNum = 0;
    this.highlightArr = [];
}

TPaint.prototype.paint = function(node) {
    if (!node.parent || node.parent.children.length == 2) {
        node.container = this.makeContainer(node);
    }
    else {
        node.container = node.parent.container;
    }
    node.div = this.nodeMake(node);
    node.container.appendChild(node.div);
    node.div.style.top = node.container.h + "px";
    node.container.h += node.div.offsetHeight + 3; 
    if (node.children.length == 0) {
        node.container.h += this.branchPadding;
    }
    if (node.spanFormula.offsetWidth > node.container.formulaWidth) {
        node.container.formulaWidth = node.spanFormula.offsetWidth + 10;
        var n = node;
        do {
            n.spanFormula.style.width = node.container.formulaWidth + "px";
            n.div.style.left = -node.div.offsetWidth/2 + "px";
            n = n.parent;
        } while (n && n.container == node.container);
    }
    else {
        node.spanFormula.style.width = node.container.formulaWidth + "px";
        node.div.style.left = -node.container.w/2 + "px";
    }
    node.container.w = Math.max(node.container.w, node.div.offsetWidth);
    this.branchRepo(node);
    this.treeInView();
}

TPaint.prototype.treePaint = function() {
    var node = this.getNextUnpaintedNode();
    if (!node) {
        this.highlightNothing();
        return this.finished();
    }
    var paintNodes = this.tree.getExpansion(node);
    for (var i=0; i<paintNodes.length; i++) {
        this.paint(paintNodes[i]);
    }
    this.highlight(paintNodes, node.fromNodes);

    this.paintTimer = setTimeout(function(){
        this.treePaint();
    }.bind(this), this.paintInterval);
}

TPaint.prototype.stop = function() {
    clearTimeout(this.paintTimer);
}

TPaint.prototype.nodeMake = function(node) {
    var div = document.createElement('div');
    div.className = 'treeNode';

    var nodeNumberSpan = document.createElement('span');
    node.nodeNumber = ++this.currNNum;
    nodeNumberSpan.className = 'nodenumber';
    nodeNumberSpan.innerHTML = node.nodeNumber+'.';
    div.appendChild(nodeNumberSpan);
    
    node.spanFormula = document.createElement('span');
    node.spanFormula.className = 'formula '+node.container.formulaClass;
    node.spanFormula.innerHTML = node.formula.string;
    if (node.closedEnd) node.spanFormula.innerHTML += "<br><b>x</b>";
    div.appendChild(node.spanFormula);
    
    if (this.isModal) {
        var worldSpan = document.createElement('span');
        worldSpan.className = 'worldlabel';
        worldSpan.innerHTML = node.formula.world ? '('+node.formula.world+')' : '';
        div.appendChild(worldSpan);
    }

    var spanVal = document.createElement('span');
    spanVal.className = 'fromnumbers';
    var annot = node.fromNodes.map(function(n) { return n.nodeNumber; });
    if (node.fromRule) {
        var fromRule = node.fromRule.toString().substr(0,3);
        if (!['alp', 'bet', 'gam', 'del', 'mod'].includes(fromRule)) {
            annot.push(fromRule+'.');
        }
    }
    spanVal.innerHTML = annot.length>0 ? "("+annot.join(',')+")" : " ";
    div.appendChild(spanVal);

    return div;
}

TPaint.prototype.finished = function() {
}

TPaint.prototype.makeContainer = function(node) {
    var parContainer = node.parent ? node.parent.container : this.rootAnchor;
    var container = document.createElement('div');
    parContainer.appendChild(container);
    if (node.parent) parContainer.subContainers.push(container);
    container.subContainers = [];
    container.style.left = "0px";
    container.style.width = "100%";
    container.style.position = "absolute";
    container.style.top = node.parent ? parContainer.h + this.branchHeight + "px" : "0px";
    container.w = container.h = 0;
    container.str = "{ "+node+ " }" + (self.__strid ? self.__strid++ : (self.__strid = 1));
    container.formulaClass = 'fla'+this.currNNum;
    container.formulaWidth = 0;
    return container;
}

TPaint.prototype.branchRepo = function(node) {
    var parent = node.container;
    while ((parent = parent.parentNode).subContainers) {
        if (!parent.subContainers[1]) continue;
        var overlap = this.getExtend(parent);
        if (overlap) {
            var x1 = parseInt(parent.subContainers[0].style.left) - Math.ceil(overlap/2);
            var x2 = parseInt(parent.subContainers[1].style.left) + Math.ceil(overlap/2);
            parent.subContainers[0].style.left = x1 + "px";
            parent.subContainers[1].style.left = x2 + "px";
            if (parent.branchLines) {
                for (var i=0; i<parent.branchLines.length; i++) {
                    parent.removeChild(parent.branchLines[i]);
                }
            }
            var centre = this.isModal ? -8 : 0; 
            var line1 = this.drawLine(parent, centre, parent.h, x1+centre, parent.h + this.branchHeight-2);
            var line2 = this.drawLine(parent, centre, parent.h, x2+centre, parent.h + this.branchHeight-2);
            parent.branchLines = [line1, line2];
        }
    }
}

TPaint.prototype.getExtend = function(parent) {
    var overlap = 0;
    var cont1, cont2, co1s = [parent.subContainers[0]], co2s;
    parent.__x = 0; parent.__y = 0;
    while ((cont1 = co1s.shift())) {
        co2s = [parent.subContainers[1]];
        while ((cont2 = co2s.shift())) {
            cont1.__x = cont1.parentNode.__x + parseInt(cont1.style.left);
            cont1.__y = cont1.parentNode.__y + parseInt(cont1.style.top);
            cont2.__x = cont2.parentNode.__x + parseInt(cont2.style.left);
            cont2.__y = cont2.parentNode.__y + parseInt(cont2.style.top);
            if ((cont1.__y >= cont2.__y) && (cont1.__y < cont2.__y + cont2.h) ||
                (cont2.__y >= cont1.__y) && (cont2.__y < cont1.__y + cont1.h)) { 
                var overlap12 = (cont1.__x + cont1.w/2 + painter.branchPadding) - (cont2.__x - cont2.w/2);
                overlap = Math.max(overlap, overlap12);
            }
            co2s = co2s.concat(cont2.subContainers);
        }
        co1s = co1s.concat(cont1.subContainers);
    }
    return Math.floor(overlap);
}

TPaint.prototype.treeInView = function() {
    var containerMain = this.rootAnchor.firstChild;
    if (containerMain.getBoundingClientRect) {
        var midPoint = Math.round(containerMain.getBoundingClientRect()['left']);
        var winTreeRatio = window.innerWidth*1.0/(midPoint*2);
        if (winTreeRatio < 1) {
            this.scale = Math.max(winTreeRatio, 0.8);
            document.getElementById('rootAnchor').style.transform="scale("+this.scale+")";
        }
    }
    var minX = this.minXValue();
    if (minX < this.minX/this.scale) {
        var invisibleWidth = (this.minX/this.scale - minX);
        containerMain.style.left = containerMain.__x + invisibleWidth + "px";
    }
}

TPaint.prototype.minXValue = function() {
    var minX = 0;
    var cont, cons = [this.rootAnchor.firstChild];
    while ((cont = cons.shift())) {
        cont.__x = (cont.parentNode.__x || 0) + parseInt(cont.style.left);
        if (cont.__x - cont.w/2 < minX) {
            minX = cont.__x - cont.w/2;
        }
        cons = cons.concat(cont.subContainers);
    }
    return minX;
}

TPaint.prototype.getNextUnpaintedNode = function() {
    var nodes = [this.tree.nodes[0]];
    var node;
    while ((node = nodes.shift())) {
        do {
            if (!node.div) return node;
            if (node.children.length == 2) nodes.unshift(node.children[1]);
        } while ((node = node.children[0]));
    }
    return null;
}
    

TPaint.prototype.highlight = function(children, fromNodes) {
    while (this.highlightArr.length) {
        this.highlightArr.shift().div.style.backgroundColor = 'unset';
    }
    for (var i=0; i<children.length; i++) {
        children[i].div.style.backgroundColor = '#00708333';

    }
    for (var i=0; i<fromNodes.length; i++) {
        fromNodes[i].div.style.backgroundColor = '#00708366';
    }
    this.highlightArr = children.concat(fromNodes);
}

TPaint.prototype.highlightNothing = function() {
    this.highlight([], []);
}

TPaint.prototype.drawLine = function(elem, x1, y1, x2, y2) {
    var xDiff = x1 - x2;
    var yDiff = y1 - y2;
    var length = Math.sqrt(xDiff*xDiff + yDiff*yDiff);
    var s_x = (x1 + x2) / 2
    var x = s_x - length / 2;
    var y = (y1 + y2) / 2;
    var angle = Math.PI - Math.atan2(-yDiff, xDiff);
    var line = document.createElement("div");
    var styles = 'border: 1px solid #678; '
               + 'width: ' + length + 'px; '
               + 'height: 0px; '
               + '-moz-transform: rotate(' + angle + 'rad); '
               + '-webkit-transform: rotate(' + angle + 'rad); '
               + '-o-transform: rotate(' + angle + 'rad); '  
               + '-ms-transform: rotate(' + angle + 'rad); '  
               + 'position: absolute; '
               + 'top: ' + y + 'px; '
               + 'left: ' + x + 'px; ';
    line.setAttribute('style', styles);  
    elem.appendChild(line);
    return line;
}

var fVal = '';

function Symbols(str) {
    str = str.replace('&', '∧');
    str = str.replace('<->', '↔');
    str = str.replace('~', '¬');
    str = str.replace('[]', '□');
    str = str.replace(/\(A([s-z])\)/, '∀$1'); 
    str = str.replace('^', '∧');
    str = str.replace('->', '→');
    str = str.replace(' v ', ' ∨ '); 
    str = str.replace('<>', '◇');
    str = str.replace(/\(E([s-z])\)/, '∃$1'); 
    str = str.replace(/(?:^|\W)\(([s-z])\)/, '∀$1'); 
    str = str.replace(/(\\vee|\\lor)[\{ ]?\}?/g, '∨');
    str = str.replace(/(\\to|\\rightarrow)[\{ ]?\}?/g, '→');
    str = str.replace(/\\[Bb]ox[\{ ]?\}?/g, '□');
    str = str.replace(/(\\neg|\\lnot)[\{ ]?\}?/g, '¬');
    str = str.replace(/(\\wedge|\\land)[\{ ]?\}?/g, '∧');
    str = str.replace(/\\leftrightarrow[\{ ]?\}?/g, '↔');
    str = str.replace(/\\[Dd]iamond[\{ ]?\}?/g, '◇');
    return str;
}

function Toggle() {
    if (/[□◇]/.test(document.forms[0].flaField.value)) {
        document.getElementById('accessibilitySpan').style.display = 'inline-block';
    }
    else {
        document.getElementById('accessibilitySpan').style.display = 'none';
    }
}

function updateInput() {
    var os = document.forms[0].flaField.value;
    if (os == fVal) {
        return true;
    }
    cposition = this.selectionStart;
    fVal = Symbols(os);  
    var difference = os.length - fVal.length
    document.forms[0].flaField.value = fVal;
    this.selectionEnd = cposition - difference;
    Toggle();
}

document.querySelectorAll('.symbutton').forEach(function(elem) {
    elem.onclick = function(e) {
        var field = document.forms[0].flaField;
        var cmd = this.innerHTML;
        field.insertAtCaret(cmd);
        Toggle();
    }
});

document.forms[0].flaField.insertAtCaret = function(str) {
   if (document.selection) {
      this.focus();
      sel = document.selection.createRange();
      sel.text = str;
      this.focus();
   }
   else if (this.selectionStart || this.selectionStart === 0) {
      
      var startPos = this.selectionStart;
      var endPos = this.selectionEnd;
      var TopScroll = this.TopScroll;
      var valu = this.value; 
      this.value = valu.substring(0, startPos)+str+valu.substring(endPos,valu.length);
      this.focus();
      this.selectionStart = startPos + str.length;
      this.selectionEnd = startPos + str.length;
      this.TopScroll = TopScroll;
   } 
   else {
      this.value += str;
      this.focus();
   }
}

var prover = null;
function beginProof() {
    var input = document.forms[0].flaField.value;
    var parser = new Parser();
    try {
        var parsedInput = parser.parseInput(input);
        var premises = parsedInput[0];
        var conclusion = parsedInput[1];
        var initFormulas = premises.concat([conclusion.negate()]);
    }
    catch (e) {
        alert(e);
        return false;
    }
    document.getElementById("intro").style.display = "none";
    document.getElementById("backtostartpage").style.display = "block";
    document.getElementById("model").style.display = "none";
    document.getElementById("status").style.display = "block";
    document.getElementById("rootAnchor").style.display = "none";
    document.getElementById("status").innerHTML = "<div id='working'>working</div>";
    var accessConstraintsArr = [];
    if (parser.isModal) {
        document.querySelectorAll('.accCheckbox').forEach(function(elem) {
            if (elem.checked) {
                accessConstraintsArr.push(elem.id);
            }
        });
    }
    prover = new Prover(initFormulas, parser, accessConstraintsArr);
    prover.onfinished = function(treeClosed) {
        var Span_conclusion = "<span class='formula'>"+conclusion+"</span>";
        if (initFormulas.length == 1) {
            var summ = Span_conclusion + " is " + (treeClosed ? "a tautology." : "not a tautology.");
        }
        else {
            var summ = premises.map(function(f){
                return "<span class='formula'>"+f+"</span>";
            }).join(', ') + (treeClosed ? " entails " : " does not entail ") + Span_conclusion + ".";
        }
        document.getElementById("status").innerHTML = summ;
        var sTree = new STree(this.tree, parser); 
        if (!treeClosed) {
            if (this.counterModel) {
                }
            return; 
        }
        if (parser.isModal) {
            sTree.createModel();
        }
        document.getElementById("rootAnchor").style.display = "block";
        self.painter = new TPaint(sTree, document.getElementById("rootAnchor"));
        self.painter.treePaint();
    }
    setTimeout(function(){
        prover.start();
    }, 1);
    return false;
}   
onload = function(e) {
    updateInput();
    document.forms[0].flaField.onkeyup = updateInput;
    document.forms[0].onsubmit = function(e) {
        hashSet();
        beginProof();
        return false;
    }
    if (location.hash.length > 0) {
        Change_Hash();
    }
}

var hashScript = false;
function hashSet() {
    hashScript = true;
    var hash = document.forms[0].flaField.value;
    var accessConstraintsArr = [];
    document.querySelectorAll('.accCheckbox').forEach(function(elem) {
        if (elem.checked) {
            accessConstraintsArr.push(elem.id);
        }
    });
    if (accessConstraintsArr.length > 0) {
        hash += '||'+accessConstraintsArr.join('|');
    }
    location.hash = hash;
}

window.onChange_Hash = Change_Hash;

function Change_Hash() {
    if (prover) prover.stop();
    if (hashScript) {
        hashScript = false;
        return;
    }
    if (location.hash.length == 0) {
        document.getElementById("intro").style.display = "block";
        document.getElementById("model").style.display = "none";
        document.getElementById("rootAnchor").style.display = "none";
        document.getElementById("backtostartpage").style.display = "none";
        document.getElementById("status").style.display = "none";
    }
    else {
        var hash = decodeURIComponent(location.hash.substr(1).replace(/\+/g, '%20'));
        var partHash = hash.split('||');
        document.forms[0].flaField.value = partHash[0];
        var accessConstraintsArr = partHash[1] ? partHash[1].split('|') : [];
        document.querySelectorAll('.accCheckbox').forEach(function(elem) {
            elem.checked = accessConstraintsArr.includes(elem.id); 
        });
        Toggle();
        beginProof();
    }
}
