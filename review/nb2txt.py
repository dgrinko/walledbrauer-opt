"""Convert a Mathematica .nb file into readable linear text (Input/Output cells)."""
import re
import sys

SPECIAL = {
    'Lambda': 'λ', 'lambda': 'λ', 'Mu': 'μ', 'mu': 'μ', 'Alpha': 'α', 'Beta': 'β',
    'Gamma': 'γ', 'Delta': 'δ', 'CapitalDelta': 'Δ', 'CurlyEpsilon': 'ε', 'Epsilon': 'ϵ',
    'Rho': 'ρ', 'Sigma': 'σ', 'CapitalSigma': 'Σ', 'Tau': 'τ', 'Pi': 'π', 'Theta': 'θ',
    'Phi': 'ϕ', 'CurlyPhi': 'φ', 'Psi': 'ψ', 'Omega': 'ω', 'Nu': 'ν', 'Kappa': 'κ',
    'Eta': 'η', 'Chi': 'χ', 'Xi': 'ξ', 'Zeta': 'ζ', 'CapitalLambda': 'Λ', 'CapitalPi': 'Π',
    'CapitalOmega': 'Ω', 'CapitalPhi': 'Φ', 'CapitalPsi': 'Ψ', 'CapitalGamma': 'Γ',
    'CapitalTheta': 'Θ', 'CapitalXi': 'Ξ', 'Iota': 'ι', 'Upsilon': 'υ',
    'IndentingNewLine': '\n', 'NewLine': '\n', 'Equal': '==', 'Rule': '->',
    'RuleDelayed': ':>', 'Element': '∈', 'Times': '×', 'Infinity': '∞',
    'LessEqual': '<=', 'GreaterEqual': '>=', 'NotEqual': '!=', 'And': '&&', 'Or': '||',
    'Transpose': 'ᵀ', 'ConjugateTranspose': '†', 'Dagger': '†', 'Conjugate': '*',
    'Function': '|->', 'InvisibleSpace': '', 'InvisibleTimes': '', 'InvisibleComma': '',
    'Placeholder': '□', 'ImaginaryI': 'I', 'ExponentialE': 'E', 'DifferentialD': 'd',
    'TensorProduct': '⊗', 'CircleTimes': '⊗', 'Dash': '-', 'LongDash': '—',
    'Cross': '×', 'Ellipsis': '…', 'CenterDot': '·', 'RightArrow': '→',
    'LeftArrow': '←', 'Equivalent': '⇔', 'Implies': '⇒', 'Not': '!', 'Hacek': 'ˇ',
    'Bullet': '•', 'Diameter': '∅', 'EmptySet': '∅', 'Degree': '°', 'Minus': '-',
    'Sum': 'Σ', 'Product': 'Π', 'Integral': '∫', 'PartialD': '∂', 'Mod': 'mod',
    'VerticalSeparator': '|', 'LeftAngleBracket': '<', 'RightAngleBracket': '>',
    'LeftDoubleBracket': '[[', 'RightDoubleBracket': ']]', 'Prime': "'",
    'Precedes': '≺', 'Succeeds': '≻', 'NonBreakingSpace': ' ', 'ThinSpace': ' ',
    'VeryThinSpace': ' ', 'MediumSpace': ' ', 'ThickSpace': ' ', 'SpanFromLeft': '',
    'SpanFromAbove': '', 'SpanFromBoth': '', 'Square': '□', 'Vee': '∨', 'Wedge': '∧',
    'Union': '∪', 'Intersection': '∩', 'Subset': '⊂', 'SubsetEqual': '⊆',
    'Superset': '⊃', 'Distributed': '~', 'Rule ': '->', 'AlignmentMarker': '',
    'LeftCeiling': '⌈', 'RightCeiling': '⌉', 'LeftFloor': '⌊', 'RightFloor': '⌋',
    'Rho ': 'ρ', 'ScriptCapitalL': '𝓛', 'ScriptCapitalP': '𝓟', 'ScriptCapitalH': '𝓗',
    'ScriptCapitalB': '𝓑', 'ScriptCapitalA': '𝓐', 'ScriptCapitalC': '𝓒',
    'ScriptCapitalD': '𝓓', 'ScriptCapitalE': '𝓔', 'ScriptCapitalF': '𝓕',
    'ScriptCapitalM': '𝓜', 'ScriptCapitalN': '𝓝', 'ScriptCapitalO': '𝓞',
    'ScriptCapitalR': '𝓡', 'ScriptCapitalS': '𝓢', 'ScriptCapitalT': '𝓣',
    'ScriptCapitalU': '𝓤', 'ScriptCapitalV': '𝓥', 'ScriptCapitalW': '𝓦',
    'ScriptCapitalX': '𝓧', 'DoubleStruckCapitalC': 'ℂ', 'DoubleStruckCapitalR': 'ℝ',
    'DoubleStruckCapitalZ': 'ℤ', 'DoubleStruckCapitalN': 'ℕ', 'DoubleStruckCapitalQ': 'ℚ',
    'Chi ': 'χ', 'ScriptL': 'ℓ', 'Ell': 'ℓ', 'HBar': 'ℏ', 'Micro': 'µ', 'Angstrom': 'Å',
}


def unescape(s):
    def rep(m):
        name = m.group(1)
        return SPECIAL.get(name, '\\[' + name + ']')
    s = re.sub(r'\\\[([A-Za-z]+)\]', rep, s)
    s = re.sub(r'\\:([0-9a-fA-F]{4})', lambda m: chr(int(m.group(1), 16)), s)
    s = s.replace('\\<', '').replace('\\>', '')
    return s


# ---------------- tokenizer / parser for the .nb expression syntax ---------------
TOK = re.compile(r'''
    (?P<ws>\s+|\(\*.*?\*\))
  | (?P<str>"(?:[^"\\]|\\.)*")
  | (?P<num>\d+\.?\d*`?[\d.]*(?:\*\^-?\d+)?)
  | (?P<sym>[A-Za-z$][A-Za-z0-9$`]*|\#\d*)
  | (?P<op><\||\|>|->|:>|\[|\]|\{|\}|\(|\)|,|==|=|\+|-|\*|/|&|\^|;|\.|<|>|!|\?|@|_)
''', re.S | re.X)


def strip_heads(text, heads=('GraphicsBox[', 'Graphics3DBox[')):
    """Replace the arguments of graphics boxes by nothing (bracket matching, string aware)."""
    out = []
    i = 0
    n = len(text)
    while i < n:
        hit = None
        for h in heads:
            if text.startswith(h, i):
                hit = h
                break
        if hit is None:
            out.append(text[i])
            i += 1
            continue
        out.append(hit)
        j = i + len(hit)
        depth = 1
        in_str = False
        while depth:
            c = text[j]
            if in_str:
                if c == '\\':
                    j += 1
                elif c == '"':
                    in_str = False
            elif c == '"':
                in_str = True
            elif c == '[':
                depth += 1
            elif c == ']':
                depth -= 1
            j += 1
        out.append(']')
        i = j
    return ''.join(out)


def tokenize(text):
    pos = 0
    out = []
    n = len(text)
    while pos < n:
        m = TOK.match(text, pos)
        if not m:
            raise ValueError('bad char at %d: %r' % (pos, text[pos:pos + 50]))
        pos = m.end()
        kind = m.lastgroup
        if kind == 'ws':
            continue
        out.append((kind, m.group()))
    return out


class P:
    def __init__(self, toks):
        self.t = toks
        self.i = 0

    def peek(self):
        return self.t[self.i] if self.i < len(self.t) else (None, None)

    def take(self):
        tok = self.t[self.i]
        self.i += 1
        return tok

    def expr(self):
        left = self.atom()
        while True:
            k, v = self.peek()
            if v in ('->', ':>'):
                self.take()
                right = self.expr()
                left = ('Rule', [left, right])
            elif k in ('sym', 'num') or v == '(':
                right = self.atom()
                left = ('Arith', [left, ' ', right])
            elif v == '&':
                self.take()
                left = ('Arith', [left, '&', ('sym', '')])
            elif v in ('+', '-', '*', '/', '^', '=', '==', '.', '<', '>', '?', '@', '_'):
                # arithmetic in options (e.g. 3.85*^9 or sizes); keep as raw
                self.take()
                right = self.atom()
                left = ('Arith', [left, v, right])
            else:
                return left

    def atom(self):
        k, v = self.take()
        if v == '(':
            inner = self.expr()
            assert self.take()[1] == ')'
            node = inner
        elif v == '<|':
            items = self.seq('|>')
            node = ('List', items)
        elif v == '{':
            items = self.seq('}')
            node = ('List', items)
        elif v == '-':
            node = ('Neg', [self.atom()])
        elif k in ('str', 'num'):
            node = (k, v)
        elif k == 'sym':
            node = ('sym', v)
        else:
            raise ValueError('unexpected %r at %d' % (v, self.i))
        while self.peek()[1] == '[':
            self.take()
            args = self.seq(']')
            node = ('Call', node, args)
        return node

    def seq(self, close):
        items = []
        if self.peek()[1] == close:
            self.take()
            return items
        while True:
            items.append(self.expr())
            k, v = self.take()
            if v == close:
                return items
            if v != ',':
                raise ValueError('expected , got %r' % v)


# ---------------- boxes -> linear text ---------------

def head(node):
    if node[0] == 'Call' and node[1][0] == 'sym':
        return node[1][1]
    return None


def boxes(node):
    t = node[0]
    if t == 'str':
        s = node[1][1:-1]
        # a box string; escaped quotes denote string literals
        s = s.replace('\\"', '"').replace('\\\\', '\\')
        return unescape(s)
    if t == 'num':
        return node[1]
    if t == 'sym':
        return node[1]
    if t == 'List':
        return ''.join(boxes(x) for x in node[1])
    if t == 'Neg':
        return '-' + boxes(node[1][0])
    if t == 'Rule':
        return boxes(node[1][0]) + '->' + boxes(node[1][1])
    if t == 'Arith':
        return boxes(node[1][0]) + node[1][1] + boxes(node[1][2])
    h = head(node)
    args = node[2]
    if h == 'RowBox':
        return boxes(args[0])
    if h in ('BoxData',):
        a = args[0]
        if a[0] == 'List':
            return '\n'.join(boxes(x) for x in a[1])
        return boxes(a)
    if h == 'SuperscriptBox':
        return '(' + boxes(args[0]) + ')^(' + boxes(args[1]) + ')'
    if h == 'SubscriptBox':
        return boxes(args[0]) + '_' + boxes(args[1])
    if h == 'SubsuperscriptBox':
        return boxes(args[0]) + '_' + boxes(args[1]) + '^' + boxes(args[2])
    if h == 'FractionBox':
        return '(' + boxes(args[0]) + ')/(' + boxes(args[1]) + ')'
    if h == 'SqrtBox':
        return 'Sqrt[' + boxes(args[0]) + ']'
    if h == 'RadicalBox':
        return 'Surd[' + boxes(args[0]) + ',' + boxes(args[1]) + ']'
    if h == 'UnderoverscriptBox':
        return boxes(args[0]) + '_{' + boxes(args[1]) + '}^{' + boxes(args[2]) + '}'
    if h in ('UnderscriptBox',):
        return boxes(args[0]) + '_{' + boxes(args[1]) + '}'
    if h in ('OverscriptBox',):
        return boxes(args[0]) + '^{' + boxes(args[1]) + '}'
    if h in ('TagBox', 'StyleBox', 'InterpretationBox', 'FormBox', 'ButtonBox',
             'AdjustmentBox', 'FrameBox', 'PaneBox', 'ItemBox', 'TooltipBox',
             'DynamicBox', 'PaneSelectorBox', 'Cell', 'TextData', 'ErrorBox',
             'TemplateBox', 'DynamicModuleBox', 'PanelBox', 'NamespaceBox'):
        if h == 'TemplateBox':
            return 'Template' + '[' + ', '.join(boxes(x) for x in args[:1]) + ']'
        if h == 'InterpretationBox':
            return boxes(args[0])
        return boxes(args[0])
    if h == 'GridBox':
        rows = args[0]
        if rows[0] == 'List':
            return '{' + ', '.join('{' + ', '.join(boxes(c) for c in r[1]) + '}' if r[0] == 'List' else boxes(r) for r in rows[1]) + '}'
    if h in ('GraphicsBox', 'Graphics3DBox', 'RasterBox', 'GraphicsComplexBox'):
        return '<<Graphics>>'
    if h == 'CheckboxBox':
        return '<<Checkbox>>'
    # generic
    return (h or '?') + '[' + ', '.join(boxes(x) for x in args) + ']'


def cell_style(cell_args):
    for a in cell_args[1:]:
        if a[0] == 'str':
            return a[1].strip('"')
    return None


def walk_cells(node, out):
    if node[0] == 'Call':
        h = head(node)
        if h == 'Cell':
            args = node[2]
            style = cell_style(args)
            content = args[0] if args else None
            if content is not None and content[0] == 'Call' and head(content) == 'CellGroupData':
                for c in content[2][0][1]:
                    walk_cells(c, out)
                return
            label = None
            for a in args[1:]:
                if a[0] == 'Rule' and a[1][0] == ('sym', 'CellLabel'):
                    label = a[1][1][1].strip('"')
            try:
                txt = boxes(content) if content is not None else ''
            except Exception as e:  # noqa
                txt = '<<unparsable: %s>>' % e
            out.append((style, label, txt))
            return
        for a in node[2]:
            walk_cells(a, out)
    elif node[0] == 'List':
        for a in node[1]:
            walk_cells(a, out)


def main(path, maxout=3000):
    text = open(path, encoding='utf-8', errors='replace').read()
    start = text.index('Notebook[')
    end = text.rfind('(* End of Notebook Content *)')
    body = re.sub(r'(?<!\\)\\\r?\n', '', text[start:end])
    body = strip_heads(body)
    toks = tokenize(body)
    tree = P(toks).expr()
    cells = []
    walk_cells(tree, cells)
    for style, label, txt in cells:
        if style in ('Output', 'Print', 'Message'):
            if len(txt) > maxout:
                txt = txt[:maxout] + ' ...<<%d chars truncated>>' % (len(txt) - maxout)
        print('=' * 8, style, label or '')
        print(txt)


if __name__ == '__main__':
    main(sys.argv[1], int(sys.argv[2]) if len(sys.argv) > 2 else 3000)
