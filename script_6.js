function TPaint(sTree, rootAnchor) {
  this.paintInterval = 200;
  this.branchPadding =
    window.innerWidth < 500 ? 0 : window.innerWidth < 800 ? 20 : 30;
  this.branchingHeight = 40;
  this.nodeHiParentCSS = 'treeNodeHiParent';
  this.nodeHiChildCSS = 'treeNodeHiChild';
  this.tree = sTree;
  this.isModal = sTree.parser.isModal;
  this.rootAnchor = rootAnchor;
  this.rootAnchor.innerHTML = '';
  this.minX = this.branchPadding / 2 - rootAnchor.offsetLeft;
  this.scale = 1;
  this.curNodeNumber = 0;
  this.highlighted = [];
}

TPaint.prototype.paint = function (node) {
  if (!node.parent || node.parent.children.length == 2) {
    node.container = this.makeContainer(node);
  } else {
    node.container = node.parent.container;
  }
  node.div = this.makeNode(node);
  node.container.appendChild(node.div);
  node.div.style.top = node.container.h + 'px';
  node.container.h += node.div.offsetHeight + 3;
  if (node.children.length == 0) {
    node.container.h += this.branchPadding;
  }
  if (node.formulaSpan.offsetWidth > node.container.formulaWidth) {
    node.container.formulaWidth = node.formulaSpan.offsetWidth + 10;
    var n = node;
    do {
      n.formulaSpan.style.width = node.container.formulaWidth + 'px';
      n.div.style.left = -node.div.offsetWidth / 2 + 'px';
      n = n.parent;
    } while (n && n.container == node.container);
  } else {
    node.formulaSpan.style.width = node.container.formulaWidth + 'px';
    node.div.style.left = -node.container.w / 2 + 'px';
  }
  node.container.w = Math.max(node.container.w, node.div.offsetWidth);
  this.branchReposition(node);
  this.treeInView();
};

TPaint.prototype.treePaint = function () {
  var node = this.getNextUnpaintedNode();
  if (!node) {
    this.highlightNothing();
    return this.finished();
  }
  var paintNodes = this.tree.getExpansion(node);
  for (var i = 0; i < paintNodes.length; i++) {
    this.paint(paintNodes[i]);
  }
  this.highlight(paintNodes, node.fromNodes);

  this.paintTimer = setTimeout(
    function () {
      this.treePaint();
    }.bind(this),
    this.paintInterval
  );
};

TPaint.prototype.stop = function () {
  clearTimeout(this.paintTimer);
};

TPaint.prototype.makeNode = function (node) {
  var div = document.createElement('div');
  div.className = 'treeNode';

  var nodeNumberSpan = document.createElement('span');
  node.nodeNumber = ++this.curNodeNumber;
  nodeNumberSpan.className = 'nodenumber';
  nodeNumberSpan.innerHTML = node.nodeNumber + '.';
  div.appendChild(nodeNumberSpan);

  node.formulaSpan = document.createElement('span');
  node.formulaSpan.className = 'formula ' + node.container.formulaClass;
  node.formulaSpan.innerHTML = node.formula.string;
  if (node.closedEnd) node.formulaSpan.innerHTML += '<br><b>x</b>';
  div.appendChild(node.formulaSpan);

  if (this.isModal) {
    var worldSpan = document.createElement('span');
    worldSpan.className = 'worldlabel';
    worldSpan.innerHTML = node.formula.world
      ? '(' + node.formula.world + ')'
      : '';
    div.appendChild(worldSpan);
  }

  var spanVal = document.createElement('span');
  spanVal.className = 'fromnumbers';
  var annot = node.fromNodes.map(function (n) {
    return n.nodeNumber;
  });
  if (node.fromRule) {
    var fromRule = node.fromRule.toString().substr(0, 3);
    if (!['alp', 'bet', 'gam', 'del', 'mod'].includes(fromRule)) {
      annot.push(fromRule + '.');
    }
  }
  spanVal.innerHTML = annot.length > 0 ? '(' + annot.join(',') + ')' : ' ';
  div.appendChild(spanVal);

  return div;
};

TPaint.prototype.finished = function () {};

TPaint.prototype.makeContainer = function (node) {
  var parContainer = node.parent ? node.parent.container : this.rootAnchor;
  var container = document.createElement('div');
  parContainer.appendChild(container);
  if (node.parent) parContainer.subContainers.push(container);
  container.subContainers = [];
  container.style.left = '0px';
  container.style.width = '100%';
  container.style.position = 'absolute';
  container.style.top = node.parent
    ? parContainer.h + this.branchingHeight + 'px'
    : '0px';
  container.w = container.h = 0;
  container.str =
    '{ ' + node + ' }' + (self.__strid ? self.__strid++ : (self.__strid = 1));
  container.formulaClass = 'fla' + this.curNodeNumber;
  container.formulaWidth = 0;
  return container;
};

TPaint.prototype.branchReposition = function (node) {
  var par = node.container;
  while ((par = par.parentNode).subContainers) {
    if (!par.subContainers[1]) continue;
    var overlap = this.getExtend(par);
    if (overlap) {
      var x1 =
        parseInt(par.subContainers[0].style.left) - Math.ceil(overlap / 2);
      var x2 =
        parseInt(par.subContainers[1].style.left) + Math.ceil(overlap / 2);
      par.subContainers[0].style.left = x1 + 'px';
      par.subContainers[1].style.left = x2 + 'px';
      if (par.branchLines) {
        for (var i = 0; i < par.branchLines.length; i++) {
          par.removeChild(par.branchLines[i]);
        }
      }
      var centre = this.isModal ? -8 : 0;
      var line1 = this.drawLine(
        par,
        centre,
        par.h,
        x1 + centre,
        par.h + this.branchingHeight - 2
      );
      var line2 = this.drawLine(
        par,
        centre,
        par.h,
        x2 + centre,
        par.h + this.branchingHeight - 2
      );
      par.branchLines = [line1, line2];
    }
  }
};

TPaint.prototype.getExtend = function (par) {
  var overlap = 0;
  var co1,
    co2,
    co1s = [par.subContainers[0]],
    co2s;
  par.__x = 0;
  par.__y = 0;
  while ((co1 = co1s.shift())) {
    co2s = [par.subContainers[1]];
    while ((co2 = co2s.shift())) {
      co1.__x = co1.parentNode.__x + parseInt(co1.style.left);
      co1.__y = co1.parentNode.__y + parseInt(co1.style.top);
      co2.__x = co2.parentNode.__x + parseInt(co2.style.left);
      co2.__y = co2.parentNode.__y + parseInt(co2.style.top);
      if (
        (co1.__y >= co2.__y && co1.__y < co2.__y + co2.h) ||
        (co2.__y >= co1.__y && co2.__y < co1.__y + co1.h)
      ) {
        var overlap12 =
          co1.__x + co1.w / 2 + painter.branchPadding - (co2.__x - co2.w / 2);
        overlap = Math.max(overlap, overlap12);
      }
      co2s = co2s.concat(co2.subContainers);
    }
    co1s = co1s.concat(co1.subContainers);
  }
  return Math.floor(overlap);
};

TPaint.prototype.treeInView = function () {
  var mainContainer = this.rootAnchor.firstChild;
  if (mainContainer.getBoundingClientRect) {
    var midPoint = Math.round(mainContainer.getBoundingClientRect()['left']);
    var winTreeRatio = (window.innerWidth * 1.0) / (midPoint * 2);
    if (winTreeRatio < 1) {
      this.scale = Math.max(winTreeRatio, 0.8);
      document.getElementById('rootAnchor').style.transform =
        'scale(' + this.scale + ')';
    }
  }
  var minX = this.minXValue();
  if (minX < this.minX / this.scale) {
    var invisibleWidth = this.minX / this.scale - minX;
    mainContainer.style.left = mainContainer.__x + invisibleWidth + 'px';
  }
};

TPaint.prototype.minXValue = function () {
  var minX = 0;
  var con,
    cons = [this.rootAnchor.firstChild];
  while ((con = cons.shift())) {
    con.__x = (con.parentNode.__x || 0) + parseInt(con.style.left);
    if (con.__x - con.w / 2 < minX) {
      minX = con.__x - con.w / 2;
    }
    cons = cons.concat(con.subContainers);
  }
  return minX;
};

TPaint.prototype.getNextUnpaintedNode = function () {
  var nodes = [this.tree.nodes[0]];
  var node;
  while ((node = nodes.shift())) {
    do {
      if (!node.div) return node;
      if (node.children.length == 2) nodes.unshift(node.children[1]);
    } while ((node = node.children[0]));
  }
  return null;
};

TPaint.prototype.highlight = function (children, fromNodes) {
  while (this.highlighted.length) {
    this.highlighted.shift().div.style.backgroundColor = 'unset';
  }
  for (var i = 0; i < children.length; i++) {
    children[i].div.style.backgroundColor = '#00708333';
  }
  for (var i = 0; i < fromNodes.length; i++) {
    fromNodes[i].div.style.backgroundColor = '#00708366';
  }
  this.highlighted = children.concat(fromNodes);
};

TPaint.prototype.highlightNothing = function () {
  this.highlight([], []);
};

TPaint.prototype.drawLine = function (el, x1, y1, x2, y2) {
  var p = x1 - x2;
  var q = y1 - y2;
  var length = Math.sqrt(p * p + q * q);
  var s_x = (x1 + x2) / 2;
  var x = s_x - length / 2;
  var y = (y1 + y2) / 2;
  var angle = Math.PI - Math.atan2(-q, p);
  var line = document.createElement('div');
  var styles =
    'border: 1px solid #678; ' +
    'width: ' +
    length +
    'px; ' +
    'height: 0px; ' +
    '-moz-transform: rotate(' +
    angle +
    'rad); ' +
    '-webkit-transform: rotate(' +
    angle +
    'rad); ' +
    '-o-transform: rotate(' +
    angle +
    'rad); ' +
    '-ms-transform: rotate(' +
    angle +
    'rad); ' +
    'position: absolute; ' +
    'top: ' +
    y +
    'px; ' +
    'left: ' +
    x +
    'px; ';
  line.setAttribute('style', styles);
  el.appendChild(line);
  return line;
};

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
  str = str.replace(/\\exists[\{ ]?\}?/g, '∃');
  str = str.replace(/(\\vee|\\lor)[\{ ]?\}?/g, '∨');
  str = str.replace(/(\\to|\\rightarrow)[\{ ]?\}?/g, '→');
  str = str.replace(/\\[Bb]ox[\{ ]?\}?/g, '□');
  str = str.replace(/\\forall[\{ ]?\}?/g, '∀');
  str = str.replace(/(\\neg|\\lnot)[\{ ]?\}?/g, '¬');
  str = str.replace(/(\\wedge|\\land)[\{ ]?\}?/g, '∧');
  str = str.replace(/\\leftrightarrow[\{ ]?\}?/g, '↔');
  str = str.replace(/\\[Dd]iamond[\{ ]?\}?/g, '◇');
  return str;
}

function Toggle() {
  if (/[□◇]/.test(document.forms[0].flaField.value)) {
    document.getElementById('accessibilitySpan').style.display = 'inline-block';
  } else {
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
  var difference = os.length - fVal.length;
  document.forms[0].flaField.value = fVal;
  this.selectionEnd = cposition - difference;
  Toggle();
}

document.querySelectorAll('.iconButton').forEach(function (el) {
  el.onclick = function (e) {
    var field = document.forms[0].flaField;
    var cmd = this.innerHTML;
    field.insertAtCaret(cmd);
    Toggle();
  };
});

document.forms[0].flaField.insertAtCaret = function (str) {
  if (document.selection) {
    this.focus();
    sel = document.selection.createRange();
    sel.text = str;
    this.focus();
  } else if (this.selectionStart || this.selectionStart === 0) {
    var StartPosition = this.selectionStart;
    var EndPosition = this.selectionEnd;
    var TopScroll = this.TopScroll;
    var val = this.value;
    this.value =
      val.substring(0, StartPosition) +
      str +
      val.substring(EndPosition, val.length);
    this.focus();
    this.selectionStart = StartPosition + str.length;
    this.selectionEnd = StartPosition + str.length;
    this.TopScroll = TopScroll;
  } else {
    this.value += str;
    this.focus();
  }
};

var prover = null;
function Proof_Start() {
  var input = document.forms[0].flaField.value;
  var parser = new Parser();
  try {
    var Input_Parsed = parser.parseInput(input);
    var premises = Input_Parsed[0];
    var conclusion = Input_Parsed[1];
    var initFormulas = premises.concat([conclusion.negate()]);
  } catch (e) {
    alert(e);
    return false;
  }
  document.getElementById('intro').style.display = 'none';
  document.getElementById('backtostartpage').style.display = 'block';
  document.getElementById('model').style.display = 'none';
  document.getElementById('status').style.display = 'block';
  document.getElementById('rootAnchor').style.display = 'none';
  document.getElementById('status').innerHTML =
    "<div id='working'>working</div>";
  var Access_Constraints = [];
  if (parser.isModal) {
    document.querySelectorAll('.accCheckbox').forEach(function (el) {
      if (el.checked) {
        Access_Constraints.push(el.id);
      }
    });
  }
  prover = new Prover(initFormulas, parser, Access_Constraints);
  prover.onfinished = function (treeClosed) {
    var Span_conclusion = "<span class='formula'>" + conclusion + '</span>';
    if (initFormulas.length == 1) {
      var summary =
        'THE GIVEN FORMULA   ' +
        Span_conclusion +
        ' IS ' +
        (treeClosed ? 'A TAUTOLOGY.' : 'NOT A TAUTOLOGY');
    } else {
      var summary =
        premises
          .map(function (f) {
            return "<span class='formula'>" + f + '</span>';
          })
          .join(', ') +
        (treeClosed ? ' entails ' : ' does not entail ') +
        Span_conclusion +
        '.';
    }
    document.getElementById('status').innerHTML = summary;
    var sTree = new STree(this.tree, parser);
    if (!treeClosed) {
      if (this.counterModel) {
      }
      return;
    }
    if (parser.isModal) {
      sTree.createModel();
    }
    document.getElementById('rootAnchor').style.display = 'block';
    self.painter = new TPaint(sTree, document.getElementById('rootAnchor'));
    self.painter.treePaint();
  };
  setTimeout(function () {
    prover.start();
  }, 1);
  return false;
}
onload = function (e) {
  updateInput();
  document.forms[0].flaField.onkeyup = updateInput;
  document.forms[0].onsubmit = function (e) {
    setHash();
    Proof_Start();
    return false;
  };
  if (location.hash.length > 0) {
    Change_Hash();
  }
};

var Hash_Script = false;
function setHash() {
  Hash_Script = true;
  var hash = document.forms[0].flaField.value;
  var Access_Constraints = [];
  document.querySelectorAll('.accCheckbox').forEach(function (el) {
    if (el.checked) {
      Access_Constraints.push(el.id);
    }
  });
  if (Access_Constraints.length > 0) {
    hash += '||' + Access_Constraints.join('|');
  }
  location.hash = hash;
}

window.onChange_Hash = Change_Hash;

function Change_Hash() {
  if (prover) prover.stop();
  if (Hash_Script) {
    Hash_Script = false;
    return;
  }
  if (location.hash.length == 0) {
    document.getElementById('intro').style.display = 'block';
    document.getElementById('model').style.display = 'none';
    document.getElementById('rootAnchor').style.display = 'none';
    document.getElementById('backtostartpage').style.display = 'none';
    document.getElementById('status').style.display = 'none';
  } else {
    var hash = decodeURIComponent(
      location.hash.substr(1).replace(/\+/g, '%20')
    );
    var hashparts = hash.split('||');
    document.forms[0].flaField.value = hashparts[0];
    var Access_Constraints = hashparts[1] ? hashparts[1].split('|') : [];
    document.querySelectorAll('.accCheckbox').forEach(function (el) {
      el.checked = Access_Constraints.includes(el.id);
    });
    Toggle();
    Proof_Start();
  }
}
