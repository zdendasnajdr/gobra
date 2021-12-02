lexer grammar GobraLexer;
import GoLexer;

// BEGIN GOBRA
//CURLIES : '{' (CURLIES|~[{}])* '}' ;

TRUE        : 'true';
FALSE       : 'false';
ASSERT      : 'assert';
ASSUME      : 'assume';
PRE         : 'requires';
PRESERVES   : 'preserves';
POST        : 'ensures';
INV         : 'invariant';
PURE        : 'pure';
OLD         : 'old';
FORALL      : 'forall';
EXISTS      : 'exists';
ACCESS      : 'acc';
FOLD        : 'fold';
UNFOLD      : 'unfold';
GHOST       : 'ghost';
IN          : 'in';
RANGE       : 'range';
SEQ         : 'seq';
SET         : 'set';
MSET        : 'mset';
PRED       : 'pred';
DOT_DOT     : '..';
SHARED      : 'shared';
EXCLUSIVE   : 'exclusive';
PREDICATE   : 'predicate';
// END GOBRA
