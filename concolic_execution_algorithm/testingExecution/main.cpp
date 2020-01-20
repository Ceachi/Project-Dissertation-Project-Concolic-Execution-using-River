#include "z3/include/z3.h"
#include <iostream>
#include <string>
#include <sstream>
#include <fstream>
#include <iterator> 
#include <boost/algorithm/string/split.hpp>
#include <boost/algorithm/string/classification.hpp>
#include <queue>
#include <map>
#include <set>
using namespace std;




#define file_Results "./testOutput.txt"

class Test {
public:
	std::string test_address;
	std::string taken_address;
	std::string notTaken_address;
	bool was_taken;
	std::string Z3_code;// asta este codul complet al testului ce il trimit catre evaluare
	std::string asserts;// aserturi originale venite de la River
	std::vector<std::string> variables; // aici sunt doar variabilele sale
	std::string true_test_assert; // assert pentru a pastra jumpul original
	std::string false_test_assert; // assert pentru negarea testului

	std::string jump_condition;

	bool isNegated;
	Test() {
		//isNegated = false;
		isNegated = true;
	}

	Test(const Test *test) {
		this->test_address = test->test_address;
		this->taken_address = test->taken_address;
		this->notTaken_address = test->notTaken_address;
		this->was_taken = test->was_taken;
		this->Z3_code = test->Z3_code;
		this->variables = test->variables;
		this->isNegated = test->isNegated;
		prepareJumpConditions();
	}

	void prepareJumpConditions() {
		this->true_test_assert.clear();
		this->false_test_assert.clear();
		std::string str;
		str.append(" (assert (= |");
		str.append(this->test_address);
		//this->true_test_assert.append(str).append("| #b1))");
		//this->false_test_assert.append(str).append("| #b0))");

	/*
		if(this->was_taken == true) { // nu a intrat in if
			this->false_test_assert.append(str).append("| #b1))");
		}else {
			this->false_test_assert.append(str).append("| #b0))");
		}
	*/	
		if(this->was_taken == false) {	
			this->true_test_assert.append(str).append("| #b0))");
			this->false_test_assert.append(str).append("| #b1))");
		}else {
			//str.append("| #b1))");
			this->true_test_assert.append(str).append("| #b1))");
			this->false_test_assert.append(str).append("| #b0))");
		}
	}

	void prepare() {
		this->jump_condition.clear();
		std::string str;
		str.append(" (assert (= |");
		str.append(this->test_address);

		if(this->isNegated == true) {
			this->jump_condition.append(str).append("| #b1))");
		}else {
			this->jump_condition.append(str).append("| #b0))"); // imi face if adevarat
		}

	}
	void prepareTestForModel() {
		this->Z3_code.clear();	
		for(auto i : this-> variables) {
			this->Z3_code.append(i);
		}
		this->Z3_code.append(asserts);
		this->prepareJumpConditions();

		if(this->isNegated == true) {
			this->Z3_code.append(this->false_test_assert);
		}else {
			this->Z3_code.append(this->true_test_assert);
		}
	}

	void setNegated(bool value) {
		this->isNegated = value;
	}
};


class PathConstraint {
	public:
		std::vector<Test*> constraints;
		std::string inputSeed;
		int bound;
		int score;

	PathConstraint() {
		score = 0;
	}

	PathConstraint(const PathConstraint &PC) {
		for(Test *t : PC.constraints) {
			Test *tCopy = new Test(*t);
			this->constraints.push_back(tCopy);
		}
	}
	
	std::map<std::string, int> getModelResultsInDecimals(Test *test) {
		std::string z3_string = test->Z3_code;
		std::string jump_condition = test->test_address;
		std::string condition = " (set-option :pp.bv-literals false)";
		z3_string.erase(std::remove(z3_string.begin(),z3_string.end(), '\n'), z3_string.end());
		//z3_string.insert(z3_string.size(), condition);
		z3_string.insert(0, condition);
		
		std::map<std::string, int> resultMap;
		Z3_config config = Z3_mk_config();
		Z3_context context = Z3_mk_context(config);
		Z3_solver solver = Z3_mk_solver(context);

		printf("%s /n", z3_string.c_str());
		Z3_ast fs = Z3_parse_smtlib2_string(context, z3_string.c_str(), 0, 0, 0, 0, 0, 0);
		Z3_solver_assert(context, solver, fs);
		int result_solver = Z3_solver_check ((Z3_context) context, (Z3_solver) solver);
		if(result_solver == -1) {
			// this means that Z3_code return "unsat"
			return resultMap; // return an empty Map
		}
		Z3_model model = Z3_solver_get_model ((Z3_context) context,  (Z3_solver) solver);
		
		bool found_jumpCondition = false;
		std::string jump_condition_function("(declare-fun ");
		jump_condition_function.append(jump_condition);
		jump_condition_function.append(" () (_ BitVec 1))");

		unsigned n = Z3_model_get_num_consts(context, model);
			for(unsigned i = 0; i < n; i++) {
				//unsigned Z3_api rezultat = Z3_model_get_num_funcs_decl(context, model, i);
				Z3_func_decl fd = Z3_model_get_const_decl(context, model, i);
				if (Z3_model_has_interp(context, model, fd))
				{
					Z3_ast s = Z3_model_get_const_interp(context, model, fd);

					Z3_string modelFunction = Z3_func_decl_to_string (context, fd);
					Z3_string modelFunction_value = Z3_ast_to_string(context, s);

					std::string modelFunction_string = modelFunction;//copy the content into a new address
					std::string modelFunction_value_string = modelFunction_value;
					
					// before insert the modelFunction and value in the map, let make some changes on them
					if(found_jumpCondition == false && modelFunction_string.compare(jump_condition_function) == 0) {
						
						//size_t found = modelFunction_string.find("|0xf61a0e26|");
						std::string temp("|"); temp.append(test->test_address); temp.append("|");
						size_t found = modelFunction_string.find(temp);
						if(found != std::string::npos) {
							/*
							size_t position = modelFunction_value_string.find("bv");
							std::string newString =modelFunction_value_string.substr(position+2);
							int value = atoi(newString.c_str());
							resultMap.insert(std::pair<std::string, int>("|0xf61a0e26|", value));
							*/
							size_t position = modelFunction_value_string.find("bv");
							modelFunction_value_string = modelFunction_value_string.substr(position+2);
							// Now we substract the value for s[0], for example modelFunction_value_string = "(_ bv0 8)". and we extract 8
							stringstream ss;
							/* Storing the whole string into string stream */
							ss << modelFunction_value_string; 
							/* Running loop till the end of the stream */
								string temp; 
								int value; 
								while (!ss.eof()) { 
								/* extracting word by word from stream */
										ss >> temp; 
								
										/* Checking the given word is integer or not */
										if (stringstream(temp) >> value) {
											resultMap.insert(std::pair<std::string, int>("jump_condition", value));
											break;
										}
								
										/* To save from space at the end of string */
										temp = ""; 
								} 
							found_jumpCondition = true;
						}
					}else {
						// for example modelFunction_string = " (define-fun |s[0]| () (_ BitVec 8)(_ bv0 8))"
						size_t found = modelFunction_string.find("|");
						std::string newString = modelFunction_string.substr(found+1); //"s[0]| () (_ BitVec 8))
						if(found != std::string::npos) { //"std::string::npos means not_found"
							//substract the function
							size_t nextFound = newString.find("|");
							newString = newString.substr(0, nextFound); //"s[0]"

							// substract the value

							
							// Now we substract the value for s[0], for example modelFunction_value_string = "(_ bv0 8)". and we extract 8
							stringstream ss;
							size_t position = modelFunction_value_string.find("bv");
							modelFunction_value_string = modelFunction_value_string.substr(position+2);
							/* Storing the whole string into string stream */
							ss << modelFunction_value_string; 
							/* Running loop till the end of the stream */
								string temp; 
								int value; 
								while (!ss.eof()) { 
								/* extracting word by word from stream */
										ss >> temp; 
								
										/* Checking the given word is integer or not */
										if (stringstream(temp) >> value) {
											resultMap.insert(std::pair<std::string, int>(newString, value));
											break;
										}
								
										/* To save from space at the end of string */
										temp = ""; 
								} 
						}
					}
				}

			}
		return resultMap;
	}
	Test* concatenateMultipleTests(std::vector<Test*> tests) {
		Test *concatenatedTest = new Test();
		for(Test* t : tests) {
			// append asserts
			concatenatedTest->asserts.append(t->asserts);
			// append variables
			for(auto var : t->variables) {
				concatenatedTest->variables.push_back(var);
			}	
		}

		

		// removing variables that are duplicated
		sort( concatenatedTest->variables.begin(), concatenatedTest->variables.end() );
		concatenatedTest->variables.erase( unique( concatenatedTest->variables.begin(), concatenatedTest->variables.end() ), concatenatedTest->variables.end() );

		// now we construct Z3_code
		concatenatedTest->Z3_code.clear();
		std::cout << concatenatedTest->Z3_code << endl<<endl<<endl;
		// first variables	
		for(auto i : concatenatedTest-> variables) {
				concatenatedTest->Z3_code.append(i);
			}
		std::cout << concatenatedTest->Z3_code << endl<<endl<<endl;
		// then asserts
		concatenatedTest->Z3_code.append(concatenatedTest->asserts);
		std::cout << concatenatedTest->Z3_code << endl<<endl<<endl;;
		// and now the jump_conditions based on the Tests
		for(Test* t : tests) {
			t->prepare();
			concatenatedTest->Z3_code.append(t->jump_condition);
			std::cout << concatenatedTest->Z3_code << endl<<endl<<endl;
			/*
			t->prepareJumpConditions();
			if(t->isNegated == true) {
				concatenatedTest->Z3_code.append(t->false_test_assert);
				std::cout << concatenatedTest->Z3_code << endl<<endl<<endl;;
			}else {
				concatenatedTest->Z3_code.append(t->true_test_assert);
				std::cout << concatenatedTest->Z3_code << endl<<endl<<endl;;
			}
			*/
		}
		std::cout << concatenatedTest->Z3_code << endl<<endl<<endl;;
		return concatenatedTest;
	}

	std::string GenerateNewInputs(std::vector<Test*> tests) {
		Test *concatenatedTests = concatenateMultipleTests(this->constraints);
		std::cout << concatenatedTests->Z3_code << endl;
		std::map<int, int> payloadMap; // key = pozition
		int max = 0;

		std::map<std::string, int> map = getModelResultsInDecimals(concatenatedTests);
		for( auto it = map.begin(); it != map.end(); ++it ) {
			std::string key = it->first;
			int value = it->second;
			if(key[0] == 's' && key[1] == '[') {
				key = key.substr(2);
				key.erase(std::remove(key.begin(),key.end(), ']'), key.end());
				int pozition = atoi(key.c_str());
				
				if(pozition > max) max = pozition;			
				payloadMap.insert(std::pair<int, int>(pozition, value));
				//payload[pozition] = value;
			}
		}

		std::string payload;
		for(int i = 0; i <= max; i++) {
			payload.append("?");
		}
		std::map<int, int>::iterator itr; 
		for(itr = payloadMap.begin(); itr != payloadMap.end(); ++itr) {

			// deal with extended ASCII Codes (this is just temporarry)
			if(itr->second > 127)
				 itr->second = 127;
			payload[itr->first] = itr->second;
		}

		return payload;
	}

	void generateInputSeed() {
		this->inputSeed = GenerateNewInputs(this->constraints);
	}

	bool checkSatisfialilityUntil(int j) {
		std::vector<Test*> temp;
		for(int i = 0; i <= j; i++) {
			temp.push_back(this->constraints[i]);
		}

		Test* concatenatedTests = concatenateMultipleTests(temp);

		std::map<std::string, int> map = getModelResultsInDecimals(concatenatedTests);

		if(map.size() == 0) {
			return false;
		}

		return true;
	}
};


Test* neg_Constraint(Test *test) {
	Test *currentConstraint = new Test(test);

	std::string str;
	str.append(" (assert (= |");
	str.append(currentConstraint->test_address);

	if(currentConstraint->was_taken == false) {	
		str.append("| #b1))");
	}else {
		str.append("| #b0))");
	}

	currentConstraint->Z3_code.append(str);

	return currentConstraint;
}



void executeRiver(std::string testInput) {
	printf("System call to RIVER is starting \n");
	
	std::string command("python -c 'print \"");
	command.append(testInput);
	command.append("\"' | river.tracer -p libfmi.so --annotated --z3 --exprsimplify");


	int st = system(command.c_str());

	printf("System call to RIVER finished \n");

}

// split string based on spaces
std::vector<std::string> split(char * line) {
	std::string str(line);
	using namespace boost::algorithm;
	 std::vector<std::string> tokens;
	 split(tokens, str, is_any_of(" "));
	 return tokens;
}

std::vector<int> extractIntegers(std::string str) {
	std::vector<int> numbers;
	stringstream ss;
	/* Storing the whole string into string stream */
	ss << str; 
	/* Running loop till the end of the stream */
	string temp; 
	int value; 
	while (!ss.eof()) { 
		/* extracting word by word from stream */
		ss >> temp; 
								
		/* Checking the given word is integer or not */
		if (stringstream(temp) >> value) {
			numbers.push_back(value);
		}
								
		/* To save from space at the end of string */
		temp = ""; 
	}
	return numbers;
	
}

std::vector<std::string> createVariables(Test *curretConstraint, std::vector<int> numbers) {

	int lenght = numbers[0];
	std::vector<std::string> listOfVariables;
	std::string str;
	str.append("(declare-fun |");
	str.append(curretConstraint->test_address);
	str.append("| () (_ BitVec 1))");

	listOfVariables.push_back(str);
	for(int i = 1; i < lenght + 1; i++) {
		std::string str;
		str.append("(declare-fun |s[");
		str.append(std::to_string(numbers[i]));
		str.append("]| () (_ BitVec 8))");
		listOfVariables.push_back(str);
	}

	return listOfVariables;
}

std::vector<Test*> trace_simple_parser() {
	FILE * fp;
    char * line = NULL;
    size_t len = 0;
    ssize_t read;

    fp = fopen("trace.simple.out", "r");
    if (fp == NULL)
        exit(EXIT_FAILURE);

	std::vector<Test*> pathConstraint;
	bool isNewTestCase = true;
	bool isFirstAttempt = false;
	 while ((read = getline(&line, &len, fp)) != -1) {
		std::vector<std::string> tokens = split(line);
		if(tokens[0].compare("Test:") == 0) {
			isFirstAttempt = true;
			Test *newTest = new Test();
			newTest->test_address = tokens[1].insert(0, "0x");
			newTest->taken_address = tokens[4].substr(0, tokens[4].size()-1).insert(0,"0x");// removing also the last character
			newTest->notTaken_address = tokens[6].substr(0, tokens[6].size()-1).insert(0,"0x");


			tokens[tokens.size() - 1].erase(std::remove(tokens[tokens.size() - 1].begin(), tokens[tokens.size() - 1].end(),'\n'), tokens[tokens.size() -1].end());

			if(tokens[tokens.size() - 1].compare("No")) {
				newTest->was_taken = false;
			}else {
				newTest->was_taken = true;
			}
			pathConstraint.push_back(newTest);
		}else {

			if(isFirstAttempt == true) {
				// FIRST INTERPRET HOW MANY VARIABLES S[I] ARE AND CREATE THEM
				std::string variables_side_string(line);
				std::string z3_code_side_string(line);

				size_t pozition = variables_side_string.find("(");

				variables_side_string = variables_side_string.substr(0,pozition);
				z3_code_side_string = z3_code_side_string.substr(pozition);
				//z3_code_side_string.insert(0, "(assert");

				std::vector<int> variables = extractIntegers(variables_side_string);
				pathConstraint.back()->variables =  createVariables(pathConstraint.back(), variables);

				pathConstraint.back()->Z3_code.append(z3_code_side_string);
				isFirstAttempt = false;

			}else {
				pathConstraint.back()->Z3_code.append(line);
			}
		}
    }

	if(pathConstraint.size() != 0) {
		for(Test *t : pathConstraint) {
			t->Z3_code.erase(std::remove(t->Z3_code.begin(),t->Z3_code.end(), '\n'), t->Z3_code.end());
			t->Z3_code.insert(0, " (assert");
			t->Z3_code.append(")");

			t->asserts = t->Z3_code;


		// insert variables
		for(std::string var : t->variables) {
			t->Z3_code.insert(0,var);
			t->Z3_code.insert(0, " ");
		}
		}
	}

    fclose(fp);
    if (line)
        free(line);
    //exit(EXIT_SUCCESS);
	return pathConstraint;
}


void ComputePathConstraint(PathConstraint *input) {
	executeRiver(input->inputSeed);

	std::vector<Test*> newConstraints = trace_simple_parser();
	if(input->constraints.size() != 0) {
		for(int i = 0; i <= input->bound; i++) {
			newConstraints[i]->isNegated = input->constraints[i]->isNegated;
		}
	}
	input->constraints = newConstraints;

	/*
	std::map<std::string, bool> temporaryMap; // in asta pun testele comune

	// vreau sa pastrez ce era anterior negat
	if(input->constraints.size() != 0) {
			// parcurg lista sa vad daca au vreo adresa comuna, daca da, o includ intr-un map
			for(Test* i : input->constraints) {
				for(Test *j : newConstraints) {
					if(i->test_address.compare(j->test_address) == 0) { // daca avem 2 teste la fel
						temporaryMap.insert(std::pair<std::string, bool>(i->test_address, i->isNegated));
						break;
					}
				}
			}

			input->constraints = newConstraints; // copiez noile constrangeri
			// iar la adresele comune copiez valuarea booleana isNegated
			for(Test *i : input->constraints) {				
				if(!(temporaryMap.find(i->test_address) == temporaryMap.end())) {
						// means that we found the key inside the map
						i->isNegated = temporaryMap.find(i->test_address)->second;

				}
			}
	}else {
		input->constraints = newConstraints;
	}
	*/
}
queue<PathConstraint*> ExpandExecution(PathConstraint *PC) {
	queue<PathConstraint*> childInputs;

	ComputePathConstraint(PC); // aici in PC am : constrangerile sale, boundul si inputSeed

	for(int j = PC->bound + 1; j < PC->constraints.size(); j++) {
		
		PathConstraint *newPC = new PathConstraint(*PC);
		newPC->constraints[j]->setNegated(false);

		if(newPC->checkSatisfialilityUntil(j) == true) {
			newPC->generateInputSeed();
			newPC->bound = j;
			childInputs.push(newPC);
		}
	}

	return childInputs;
}


void Score(PathConstraint *pc, std::set<string> &blockAddreses) {
	int score = 0;
	for(Test t : pc->constraints) {
		const bool is_in = blockAddreses.find(t.test_address) != blockAddreses.end();
		if(is_in == false) {
			blockAddreses.insert(t.taken_address);
			score++;
		}
	}
	pc->score = score;
}

struct comparator {
	bool operator()(PathConstraint * i, PathConstraint *j) {

		return i->score < j->score;
 }
};

void search(std::string inputSeed) {
	PathConstraint *pc = new PathConstraint();
	
	std::set<string> blockAddreses;
	pc->inputSeed = inputSeed;
	pc->bound = -1;

	//stack<PathConstraint*> workList;
	priority_queue<PathConstraint*, std::vector<PathConstraint*>, comparator> workList;
	workList.push(pc);

	std::vector<string> coverageInputs;

	while(!workList.empty())  {
		PathConstraint *input = workList.top();
		workList.pop();
		coverageInputs.push_back(input->inputSeed);
		queue<PathConstraint*> childInputs = ExpandExecution(input);

		while(!childInputs.empty()) {
			PathConstraint *child = childInputs.front(); //front()
			Score(child, blockAddreses);
			workList.push(child);
			childInputs.pop();
		}

	}

	ofstream newfile("/home/ceachi/testtools/simpletracer/experiments/testingExecution/coverageInputs.txt");
	for (string &s : coverageInputs) {
  		 cout << s << " ";
  		 newfile << s << " " << endl;
	}
}
int main() {
	search("good");



	/*
	executeRiver((unsigned char *) "ABCD");
	std::vector<Test*> tests = trace_simple_parser();

	std::string newInput = GenerateNewInputs(tests);
	printf("%s", newInput);
	*/
/*
	Test *concatenatedTest = concatenateMultipleTests(tests);
	std::map<std::string, int> map = getModelResultsInDecimals(concatenatedTest);
*/

/*
	std::vector<std::map<std::string, int>> maps;
	for(Test *test : tests) {
		Test *newTest = neg_Constraint(test);
		maps.push_back(getModelResultsInDecimals(newTest));
	}
*/
	

return 0;
}