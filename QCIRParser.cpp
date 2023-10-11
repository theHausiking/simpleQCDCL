
#include "QCIRParser.h"
#include "solver.h"

#include <iostream>
#include <sstream>
#include <fstream> 
#include <algorithm>
#include <unordered_map>

std::unordered_map<int, std::string> original_variable_names;
std::unordered_map<std::string, int> internal_variable_names;
std::unordered_map<std::string, int> original_prefix_position;

int prefixCount = 0;

/* Gate Datastructure */
QuantifierNode* firstQuantifier;
QuantifierNode* lastQuantifier;
std::unordered_map<variable, QuantifierNode> allQuantifierNodes;

std::deque<int> internal_variable_original_quantifiers;


int variables;
int innermost_universal;

std::map<std::string,int> varToIntMapping;
int currentVarIndexMapping = 1;

const std::string FORALL_QCIR = "forall";
const std::string EXISTS_QCIR = "exists";
const std::string OUTPUT_QCIR = "output";
const std::string AND_QCIR = "and";
const std::string OR_QCIR = "or";

struct cnfFormular cnfFormular = {};
struct variable outputVariableExists = variable();
struct variable outputVariableForAll = variable();

bool withQuantifierRearrange;

bool isCommand(std::string line){
    return line.front() == '#';
}

bool isExist(std::string line){
    return line.substr(0,6) == EXISTS_QCIR;
}

bool isForAll(std::string line){
    return line.substr(0,6) == FORALL_QCIR;
} 

bool isOutput(std::string line){
    return line.substr(0,6) == OUTPUT_QCIR;
}

/*
    Returns true if qNode2 is lowerLevel -> is innermost than qNode1
*/
bool isLowerLevelQuantifier(QuantifierNode* qNode1, QuantifierNode* qNode2){
    for(int i = 0; i < static_cast<int>(qNode1->levels.size()); i++){
        if(i >= static_cast<int>(qNode2->levels.size()))
            return false;
        if(qNode1->levels[i] == qNode2->levels[i]) 
            continue;
        return qNode1->levels[i] < qNode2->levels[i];
    }
    return true;
}

void readQuantifier(std::string line, bool isExists){
    int startVarPosition = line.find('(');

    std::string varString = line.substr(startVarPosition+1,line.size() - startVarPosition - 2);

    std::stringstream sStream(varString);
    std::string var;

    while (std::getline(sStream, var, ',')){
        variable currentVar = variable(var);
        quantifier quant = quantifier(currentVar, (isExists? EXISTS : FORALL));
    
        cnfFormular.quantifiers.push_back(quant);
        cnfFormular.variables.push_back(currentVar);
        varToIntMapping[var] = 2*currentVarIndexMapping + (isExists? 0 : 1);
        currentVarIndexMapping++;

        original_prefix_position[currentVar.varName] = prefixCount;

        std::vector<int> vect;
        vect.push_back(prefixCount);
        QuantifierNode currentQN = QuantifierNode(quant,vect, true); 

        allQuantifierNodes[currentVar] = currentQN;

        if(prefixCount == 0){
            firstQuantifier = &allQuantifierNodes[currentVar];
            lastQuantifier = &allQuantifierNodes[currentVar];
            lastQuantifier->next = nullptr;
        } else {
            lastQuantifier->next = &allQuantifierNodes[currentVar];
            lastQuantifier = &allQuantifierNodes[currentVar];
            lastQuantifier->next = nullptr;
        }

        prefixCount++;
    }

}

void readOutput(std::string line){
    int startVarPosition = line.find('(');

    std::string varString = line.substr(startVarPosition+1,line.size() - startVarPosition -2);

    outputVariableExists = variable(varString);
    outputVariableForAll = variable("A"+varString);

    cnfFormular.clauses.push_back(simpleClause({outputVariableExists},true));
    cnfFormular.clauses.push_back(simpleClause({outputVariableForAll},false));
} 

void rearrangeGateQuantifier(variable gate, std::vector<variable> vars, quantifierType qType){   


    if(withQuantifierRearrange){

        if(vars.size() == 0) {
            std::vector<int> v;
            v.push_back(lastQuantifier->levels[0]+1);
            QuantifierNode newGateQN = QuantifierNode(quantifier(gate,qType),v);
            allQuantifierNodes[newGateQN.quant.var.varName] = newGateQN;

            lastQuantifier->next = &allQuantifierNodes[newGateQN.quant.var.varName];
            lastQuantifier = &allQuantifierNodes[newGateQN.quant.var.varName];
            lastQuantifier->next = nullptr;
            return;
        }

        if(gate.varName[0] == 'A' && vars[0].varName[0] != 'A' && original_prefix_position.find(vars[0].varName) == original_prefix_position.end()){
            vars[0].varName = "A"+vars[0].varName;
        }

        QuantifierNode* lowestQuantifier = &allQuantifierNodes[vars[0]];

        for(variable v : vars){
            if(gate.varName[0] == 'A' && v.varName[0] != 'A' && original_prefix_position.find(v.varName) == original_prefix_position.end()){
                v.varName = "A"+v.varName;
            }

            QuantifierNode* currentQ = &allQuantifierNodes[v];

            if(isLowerLevelQuantifier(lowestQuantifier, currentQ)){
                lowestQuantifier = currentQ;
            }
        }

        std::vector<int> quantifierGateLevel = lowestQuantifier->levels;
        quantifierGateLevel.push_back(lowestQuantifier->directSuccessors.size());
        QuantifierNode newGateQN = QuantifierNode(quantifier(gate,qType),quantifierGateLevel);
        

        allQuantifierNodes[newGateQN.quant.var.varName] = newGateQN;
        lowestQuantifier->directSuccessors.push_back(&allQuantifierNodes[newGateQN.quant.var.varName]);

    } else {
        std::vector<int> v;

        v.push_back(lastQuantifier->levels[0]+1);

        QuantifierNode newGateQN = QuantifierNode(quantifier(gate,qType),v);

        allQuantifierNodes[newGateQN.quant.var.varName] = newGateQN;

        lastQuantifier->next = &allQuantifierNodes[newGateQN.quant.var.varName];
        lastQuantifier = &allQuantifierNodes[newGateQN.quant.var.varName];
        lastQuantifier->next = nullptr;
    }
}

void addQCIRClauseToDNF(variable gate, std::vector<variable> vars, bool isOr){
    std::vector<simpleClause> clauses;

    std::vector<variable> varList;
    variable negatedGate = gate;
    negatedGate.positiveValue = !gate.positiveValue;

    if(!isOr){
        varList.push_back(negatedGate);

        for(variable v : vars){
            variable negatedV = v;
            negatedV.positiveValue = !v.positiveValue;

            if(original_prefix_position.find(v.varName) == original_prefix_position.end()){
                v.varName = "A"+v.varName;
                negatedV.varName = "A"+negatedV.varName;
            }
            
            varList.push_back(v);

            std::vector<variable> helperList = {gate,negatedV};
            clauses.push_back(simpleClause(helperList,false));
        }

        clauses.push_back(simpleClause(varList,false));
    } else {
        varList.push_back(gate);

        for(variable v : vars){
            variable negatedV = v;
            negatedV.positiveValue = !v.positiveValue;

            if(original_prefix_position.find(v.varName) == original_prefix_position.end()){
                v.varName = "A"+v.varName;
                negatedV.varName = "A"+negatedV.varName;
            }

            varList.push_back(negatedV);

            std::vector<variable> helperList = {negatedGate,v};
            clauses.push_back(simpleClause(helperList,false));
        }
    
        clauses.push_back(simpleClause(varList,false));
    }

    cnfFormular.clauses.insert(cnfFormular.clauses.end(),clauses.begin(), clauses.end());

    rearrangeGateQuantifier(gate, vars,FORALL);
}

void addQCIRClauseToCNF(variable gate, std::vector<variable> vars, bool isOr){
    std::vector<simpleClause> clauses;

    std::vector<variable> varList;
    variable negatedGate = gate;
    negatedGate.positiveValue = !gate.positiveValue;

    if(isOr){
        varList.push_back(negatedGate);

        for(variable v : vars){
            variable negatedV = v;
            negatedV.positiveValue = !v.positiveValue;
            
            varList.push_back(v);

            std::vector<variable> helperList = {gate,negatedV};
            clauses.push_back(simpleClause(helperList,true));
        }

        clauses.push_back(simpleClause(varList,true));
    } else {
        varList.push_back(gate);

        for(variable v : vars){
            variable negatedV = v;
            negatedV.positiveValue = !v.positiveValue;

            varList.push_back(negatedV);

            std::vector<variable> helperList = {negatedGate,v};
            clauses.push_back(simpleClause(helperList,true));
        }
    
        clauses.push_back(simpleClause(varList,true));
    }

    cnfFormular.clauses.insert(cnfFormular.clauses.end(),clauses.begin(), clauses.end());
    
    rearrangeGateQuantifier(gate,vars,EXISTS);
}

void readGates(std::string line){
    int equalSignPosition = line.find('=');
    int startVarListPosition = line.find('(');

    variable newGate = variable(line.substr(0, equalSignPosition));

    bool isOr = line.substr(equalSignPosition+1,2) == OR_QCIR;

    std::string varString = line.substr(startVarListPosition+1,line.size() - startVarListPosition - 2);

    std::stringstream sStream(varString);
    std::string var;

    std::vector<variable> variables; 

    while (std::getline(sStream, var, ',')){
        if(var.front() == '-') {
            variables.push_back(variable(var.substr(1),false));
        } else {
            variables.push_back(variable(var));
        }
    }

    addQCIRClauseToCNF(newGate,variables,isOr);

    cnfFormular.variables.push_back(newGate);

    varToIntMapping[newGate.varName] = 2*currentVarIndexMapping;
    currentVarIndexMapping++;

    variable newGateDNF = variable("A" + newGate.varName);

    addQCIRClauseToDNF(newGateDNF,variables,isOr);

    cnfFormular.variables.push_back(newGateDNF);    

    varToIntMapping[newGateDNF.varName] = 2*currentVarIndexMapping + 1;
    currentVarIndexMapping++;
}

static void parse(std::string filename){
    std::ifstream file(filename);
    std::string currentLine;

    while(std::getline(file,currentLine)){
        currentLine.erase(
            std::remove_if(
                currentLine.begin(),
                currentLine.end(),
                [](unsigned char c) {return isspace(c);}
                ),
            currentLine.end());

        if(isCommand(currentLine)){
            std::cout << currentLine << std::endl;
            continue;
        }
        if(isExist(currentLine)){
            readQuantifier(currentLine,true);
            continue;
        }
        if(isForAll(currentLine)){
            readQuantifier(currentLine, false);
            continue;
        }
        if(isOutput(currentLine)){
            readOutput(currentLine);
            continue;
        }
        if(currentLine == ""){
            continue;
        }
        readGates(currentLine);
    }

    file.close();
}

void addNodeToQuantifiers(QuantifierNode* qNode, int* numberOfQuantifier){
    
    (*numberOfQuantifier)++;
    quantifier q = qNode->quant;
    int internalMapping = (*numberOfQuantifier)*2 + (q.type == EXISTS? 1 : 0);
    original_variable_names[internalMapping] = q.var.varName;
    internal_variable_names[q.var.varName] = internalMapping;

    if(qNode->originalPrefixVar 
    || qNode->quant.var == outputVariableExists 
    || qNode->quant.var == outputVariableForAll)
        internal_variable_original_quantifiers.push_front(internalMapping);

    if(q.type == FORALL && innermost_universal < internalMapping){
        innermost_universal = internalMapping;
    }
}

void goThroughAllDirectSuccessors(QuantifierNode* qNode, int* numberOfQuantifier){

    //Original prefix variables are already inserted
    addNodeToQuantifiers(qNode,numberOfQuantifier);

    //Add all direct successors
    for(QuantifierNode* qN : qNode->directSuccessors){
        goThroughAllDirectSuccessors(qN, numberOfQuantifier);
    }
}

void initSolver(){

    variables = currentVarIndexMapping*2; 

    //Init quantifier
    int numberOfQuantifiers = 0;    
    QuantifierNode* currentQuantifier = firstQuantifier;

    //Add all quantifiers
    while(currentQuantifier){
        goThroughAllDirectSuccessors(currentQuantifier, &numberOfQuantifiers);
        currentQuantifier = currentQuantifier->next;
    }

    initialize();

    //Init clauses
    std::vector<int> literals;
    for(simpleClause c : cnfFormular.clauses){
        for(variable v : c.literals){
            int lit = internal_variable_names[v.varName] * (v.positiveValue? 1 : -1 );
            literals.push_back(lit);
        }

        universal_existential_reduction(literals, c.isOr);
        add_clause(false,0,literals,c.isOr);
        literals.clear();
    }
}

void runParser(std::string fileName, bool rearrange){
    withQuantifierRearrange = rearrange;
    parse(fileName);
    initSolver();
    allQuantifierNodes.clear();
}