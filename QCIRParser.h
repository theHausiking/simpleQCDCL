#include<string>
#include<vector>
#include<list>
#include<map>

struct variable{
    std::string varName;
    bool positiveValue = true;

    variable(std::string var, bool posValue): varName(var), positiveValue(posValue) {}
    variable(std::string var): varName(var) {}
    variable() {}

    bool operator==(const variable& v) const {
        return v.varName == this->varName;
    }
};

template <>
struct std::hash<variable>
{
  std::size_t operator()(const variable& v) const
  {
    using std::size_t;
    using std::hash;
    using std::string;

    // Compute individual hash values for first,
    // second and third and combine them using XOR
    // and bit shifting:

    return (hash<string>()(v.varName));
  }
};


struct simpleClause{
    std::vector<variable> literals;
    bool isOr;

    simpleClause(std::vector<variable> vars, bool isOr):
        literals(vars),
        isOr(isOr) {}
};

enum quantifierType{
    EXISTS,
    FORALL
};

struct quantifier{
    variable var;
    quantifierType type;

    quantifier(){}
    quantifier(variable var, quantifierType qType): var(var), type(qType){}
};

struct cnfFormular{
    std::list<quantifier> quantifiers;
    std::vector<variable> variables;
    std::vector<simpleClause> clauses;
};

struct QuantifierNode{
    quantifier quant;
    std::vector<QuantifierNode*> directSuccessors;
    QuantifierNode* next;
    std::vector<int> levels;
    bool originalPrefixVar = false;

    QuantifierNode(){}
    QuantifierNode(quantifier q, std::vector<int> lvl): quant(q), levels(lvl){}
    QuantifierNode(quantifier q, std::vector<int> lvl, bool ogVar): quant(q), levels(lvl), originalPrefixVar(ogVar){}

};

void runParser(std::string fileName,bool rearrange);