/*
 * Copyright (C) Mohsen Zohrevandi, 2017
 *               Rida Bazzi 2019
 * Do not share this file with anyone
 */
#include <iostream>
#include <cstdio>
#include <cstdlib>
#include <cstdlib>
#include "lexer.h"
#include <stdio.h>
#include <vector> 
#include <algorithm>
#include <unordered_map>
#include <set>
#include <algorithm>
#include <list> 
#include <ostream>



using namespace std;

LexicalAnalyzer lexer;
Token t;
bool contains_useless_symbols = false;
bool first_set_calculated = false;

void parse_id();
void parse_id_list();
void parse_input();
void parse_right_hand_side();
void parse_rule();
void parse_rule_list();
void orderSymbols();
void print_generating_data();
void set_terminals_to_true();
void set_epsilons_to_true();
bool iterate_through_rules();
void determine_reachable_symbols();
bool contains_non_generating(vector<vector<string> >::iterator it, vector<string>::iterator jt);
bool set_rule_as_useless(vector<vector<string> >::iterator it, vector<string>::iterator jt);
bool contains_unreachable(vector<vector<string> >::iterator it, vector<string>::iterator jt);
bool improper_structure(vector<string>::iterator jt);
void initialize_first_sets();
void add_terminals_to_first_sets();
void add_epsilon_to_first_sets();
bool add_first_set_by_iteration();
void initialize_follow_sets();
void add_terminals_to_follow_sets();
void print_follow_sets();
void add_eof_to_follow_set();
bool add_follow_set_by_iteration();





// declaring set for terminals and non terminals
vector<string> possible_non_terminals;
vector<string> ordered_non_terminals;
vector<string> terminals;
vector<string> generating_non_terminals;
string START_SYMBOL;

unordered_map <string, vector<vector<string>>> rule_list;
vector<vector<string>> rhs_vector_container;
vector<string> rhs_symbols;

vector<string> generating_symbols_vector;
unordered_map <string, bool> generating_map;

vector<string> reachable_symbols_vector;
unordered_map <string, bool> reachable_map;
unordered_map <string, bool> non_term_map;
unordered_map <string, bool> term_map;

unordered_map <string, set<string>> first_set_map;
unordered_map <string, set<string>> follow_set_map;




void initialize_vector_and_map()
{
	int size = ordered_non_terminals.size() + terminals.size();

	for (int i = 0; i < terminals.size(); i++)
	{
		generating_symbols_vector.push_back(terminals[i]);
		generating_map.insert({ terminals[i], false });
		//reachable_map.insert({ terminals[i], true });
		term_map.insert({ terminals[i], true });
	}
	for (int i = 0; i < ordered_non_terminals.size(); i++)
	{
		generating_symbols_vector.push_back(ordered_non_terminals[i]);
		generating_map.insert({ ordered_non_terminals[i], false });
		reachable_map.insert({ ordered_non_terminals[i], false });
		non_term_map.insert({ ordered_non_terminals[i], true });


	}
	reachable_map.insert({ START_SYMBOL, true });
}


void print_generating_data()
{
	cout << "symbols vector: " << endl;
	for (auto i = generating_symbols_vector.begin(); i != generating_symbols_vector.end(); i++)
	{
		cout << *i << " ";
	}
	cout << endl << "generating vector: " << endl;
	for (auto i = generating_map.begin(); i != generating_map.end(); i++)
	{
		cout << i->first << " : ";
		cout << i->second << endl;

	}


}

void parse_input()
{
	Token t1 = lexer.GetToken();
	START_SYMBOL = t1.lexeme;
	lexer.UngetToken(t1);
	parse_rule_list();


}

void parse_rule_list()
{
	Token t1, t2;
	t1 = lexer.GetToken();
	t2 = lexer.GetToken();

	if (t1.token_type == ID && t2.token_type == ARROW)
	{
		//cout << "parsing rule\n";
		//cout << "" << t1.lexeme << " ->" << endl;
		if (std::find(possible_non_terminals.begin(), possible_non_terminals.end(), t1.lexeme) == possible_non_terminals.end()) {
			// someName not in name, add it
			possible_non_terminals.push_back(t1.lexeme);
		}


		lexer.UngetToken(t2);
		lexer.UngetToken(t1);
		parse_rule();
		rhs_symbols.erase(rhs_symbols.begin(), rhs_symbols.end());
		rhs_vector_container.erase(rhs_vector_container.begin(), rhs_vector_container.end());

		t1 = lexer.GetToken();
		t2 = lexer.GetToken();

		if (t1.token_type == ID || t2.token_type == ARROW)
		{
			lexer.UngetToken(t2);
			lexer.UngetToken(t1);
			//cout << "parsed rule\n";
			parse_rule_list();
		}
		else
		{
			return;
		}
	}
	else
	{
		cout << "Syntax error!\n";
	}
}

void addNonTerminalToMap(string non_term)
{

	if (rule_list.find(non_term) == rule_list.end()) {
		// not found
		rhs_vector_container.push_back(rhs_symbols);
		rule_list[non_term] = rhs_vector_container;
	}
	else {



		vector<string> prev_rhs_vector;
		vector<vector<string>> new_vector_container;

		for (vector<vector<string> >::iterator it = rule_list.at(non_term).begin(); it != rule_list.at(non_term).end(); ++it)
		{
			vector<string> prev_rhs_vector;
			//it is now a pointer to a vector<int>
			for (vector<string>::iterator jt = it->begin(); jt != it->end(); ++jt)
			{
				// jt is now a pointer to an integer.
				//cout << *jt;
				prev_rhs_vector.push_back(*jt);

			}
			new_vector_container.push_back(prev_rhs_vector);
			//cout << endl;
		}
		new_vector_container.push_back(rhs_symbols);


		//rule_list.erase(non_term);
		rule_list[non_term] = new_vector_container;
		//rule_list.insert({ non_term, new_vector_container });
	}
}

void parse_rule()
{
	Token t1, t2, t3;
	t1 = lexer.GetToken();
	t2 = lexer.GetToken();
	if (t1.token_type == ID && t2.token_type == ARROW)
	{
		// to get non term in order of first seen
		if (std::find(possible_non_terminals.begin(), possible_non_terminals.end(), t1.lexeme) == possible_non_terminals.end()) {
			// someName not in name, add it
			possible_non_terminals.push_back(t1.lexeme);
		}

		parse_right_hand_side();
		t3 = lexer.GetToken();
		if (t3.token_type == HASH)
		{
			//cout << "#\n";
			//cout << "ID -> RHS #\n";
			///rhs_symbols.push_back(t.lexeme);
		}
		else
		{
			cout << "Syntax error!\n";
		}
	}
	addNonTerminalToMap(t1.lexeme);


}



void parse_right_hand_side()
{
	Token t1 = lexer.GetToken();
	Token t2;

	if (t1.token_type == ID)
	{
		lexer.UngetToken(t1);
		parse_id_list();
	}
	else if (t1.token_type == HASH)
	{
		lexer.UngetToken(t1);
		//cout << "rhs = #\n";
		rhs_symbols.push_back("#");
		terminals.push_back("#");


	}
	else if (t1.token_type == DOUBLEHASH)
	{
		t2 = lexer.GetToken();
		if (t2.token_type == HASH)
		{
			rhs_symbols.push_back("#");
			lexer.UngetToken(t2);
		}

	}
}


void parse_id_list()
{
	Token t1;
	t1 = lexer.GetToken();

	if (t1.token_type == ID)
	{
		lexer.UngetToken(t1);
		parse_id();

		t1 = lexer.GetToken();

		if (t1.token_type == ID)
		{
			lexer.UngetToken(t1);
			parse_id_list();
		}
		else if (t1.token_type == HASH)
		{
			lexer.UngetToken(t1);
			return;
		}
		else
		{
			return;
		}
	}
	else
	{
		cout << "bad syntax!\n";
	}
}

void parse_id()
{
	Token t = lexer.GetToken();
	//cout << "ID = " << t.lexeme << "\n";

	// adds all RHS IDs to terminal set
	//     will remove all non term after parsing
	//     is finished
	if (std::find(possible_non_terminals.begin(), possible_non_terminals.end(), t.lexeme) == possible_non_terminals.end()) {
		// someName not in name, add it
		possible_non_terminals.push_back(t.lexeme);
	}

	if (find(terminals.begin(), terminals.end(), t.lexeme) == terminals.end()) {
		// someName not in name, add it
		terminals.push_back(t.lexeme);
	}
	rhs_symbols.push_back(t.lexeme);

}

void removeNonTermFromTermVector(string str)
{
	// remove non terms from term vector
	terminals.erase(remove(terminals.begin(), terminals.end(), str), terminals.end());
}

// read grammar
void ReadGrammar()
{

	//cout << "0\n";

	//cout << "ReadGrammar\n";
	parse_input();


}

void printmap()
{
	bool generating = true;

	string term;
	for (int i = 0; i < ordered_non_terminals.size(); i++)
	{
		term = ordered_non_terminals[i];
		for (vector<vector<string> >::iterator it = rule_list.at(term).begin(); it != rule_list.at(term).end(); ++it)
		{

			if (generating)
			{



				cout << term << " -> ";
				//it is now a pointer to a vector<int>
				for (vector<string>::iterator jt = it->begin(); jt != it->end(); ++jt)
				{


					cout << *jt << " ";

				}

				cout << endl;
			}
			generating = true;
		}

	}

}

void print_useful_only()
{
	bool generating = true;
	bool is_reachable = true;
	string full_rule = "";

	//if (reachable_map[START_SYMBOL] == false)
		//return;


	string term;
	for (int i = 0; i < ordered_non_terminals.size(); i++)
	{
		term = ordered_non_terminals[i];
		for (vector<vector<string> >::iterator it = rule_list.at(term).begin(); it != rule_list.at(term).end(); ++it)
		{


			if (reachable_map[term] && generating_map[term])
			{

				full_rule += term + " -> ";


				//it is now a pointer to a vector<int>
				for (vector<string>::iterator jt = it->begin(); jt != it->end(); ++jt)
				{


					if (contains_unreachable(it, jt))
					{
						full_rule = "";
						is_reachable = false;
						break;
						//cout << "rule skippd because has unreachable." << endl;
						//is_reachable = false;
					}
					else
					{

						full_rule += " " + *jt;
					}
				}

				if (is_reachable)
					cout << full_rule << endl;


				full_rule = "";
				is_reachable = true;
			}
			else { full_rule = ""; }
		}

	}

}

// ensure the rule has sentential form S *-> x A y



bool contains_non_generating(vector<vector<string> >::iterator it, vector<string>::iterator jt)
{
	bool found = false, flag = false;
	string str;

	// iterates the symbols in the rule, set the symbol to unreachable if non generating
	for (vector<string>::iterator jt = it->begin(); jt != it->end(); ++jt)
	{
		//str = *jt;
		//if (non_term_map.count(str) == 1)
			//found = true;


		if (generating_map[*jt] && non_term_map.count(*jt))
		{

			reachable_map[*jt] = true;
		}

	}
	//if (flag)
		//set_rule_as_useless(it, jt);
	return flag;
}

bool contains_unreachable(vector<vector<string> >::iterator it, vector<string>::iterator jt)
{
	bool flag = false;

	for (vector<string>::iterator jt = it->begin(); jt != it->end(); ++jt)
	{
		if (non_term_map[*jt])
		{
			if (reachable_map[*jt] == false)
			{
				flag = true;
			}
		}

	}
	return flag;
}

bool set_rule_as_useless(vector<vector<string> >::iterator it, vector<string>::iterator jt)
{
	for (vector<string>::iterator jt = it->begin(); jt != it->end(); ++jt)
	{	//cout << "in set reachable method: " << *jt << endl;
		//cout << "set reachable map for : " << *jt << " to false." << endl;
		reachable_map[*jt] = false;

	}
	return false;
}

void orderSymbols()
{
	for (auto i = possible_non_terminals.begin(); i != possible_non_terminals.end(); i++)
	{
		if (rule_list.find(*i) != rule_list.end()) {
			ordered_non_terminals.push_back(*i);
			removeNonTermFromTermVector(*i);
		}
	}
}


// Task 1
void printTerminalsAndNonTerminals()
{
	//  non-terminals
	for (auto i = ordered_non_terminals.begin(); i != ordered_non_terminals.end(); i++)
	{
		if (rule_list.find(*i) != rule_list.end()) {
			cout << *i << " ";

		}

	}
	// prints out terminals
	for (auto i = terminals.begin(); i != terminals.end(); i++)
	{
		if (*i != "#" && *i != "$")
			cout << *i << " ";
	}
	cout << endl;

}

void set_terminals_to_true()
{


	// iterate over all terminal, set according vector indexes to true in generating vector, bc terminals generate by default
	for (auto i = terminals.begin(); i != terminals.end(); i++)
	{
		generating_map[*i] = true;
	}



}

void set_epsilons_to_true()
{
	string str;

	string non_terminal;
	for (int i = 0; i < ordered_non_terminals.size(); i++)
	{
		non_terminal = ordered_non_terminals[i];

		for (vector<vector<string> >::iterator it = rule_list.at(non_terminal).begin(); it != rule_list.at(non_terminal).end(); ++it)
		{

			// it is now a pointer to a vector<int>
			for (vector<string>::iterator jt = it->begin(); jt != it->end(); ++jt)
			{
				str = *jt;

				// checking for epsilons
				if (str.compare("#") == 0)
				{
					//cout << "found # in non-terminal: " << non_terminal << endl;
					generating_map[non_terminal] = true;
					generating_non_terminals.push_back(non_terminal);

				}

			}
		}
	}

}


bool iterate_through_rules()
{
	// iterate through rules, updating the non term's generating map if needed. return true if changes was made to map, false if no change made. 

	bool change_made = false;
	bool generating = false;
	string symbol, non_terminal;



	// iterate through all non terminals
	for (int i = 0; i < ordered_non_terminals.size(); i++)
	{
		non_terminal = ordered_non_terminals[i];

		// iterate each vector of rules.  S -> aAb | cBd 
		// first iterate the aAb, next outer iteration will be the cBd
		for (vector<vector<string> >::iterator it = rule_list.at(non_terminal).begin(); it != rule_list.at(non_terminal).end(); ++it)
		{

			// only need to check for change on non terminal symbols that are not already considered generating
			if (generating_map[non_terminal] == false)
			{

				// checks its first lhs symbol
				//auto jt = it->begin();

				// need to check all the symbols in the rule, not just the first.
				for (vector<string>::iterator jt = it->begin(); jt != it->end(); ++jt)
				{
					symbol = *jt;

					// checking if the first symbol generates
					if (generating_map[symbol] == true)
					{
						// cout << "yes " << non_terminal << " is generating because " << symbol << " is generating." << endl;
						generating = true;
					}
					if (generating_map[symbol] == false)
					{
						// cout << "yes " << non_terminal << " is generating because " << symbol << " is generating." << endl;
						generating = false;
						break;
					}
				}
				if (generating)
				{
					generating_map[non_terminal] = true;
					generating_non_terminals.push_back(non_terminal);
					change_made = true;
				}
				generating = false;


			}

		}
	}

	return change_made;
}

void determine_reachable_symbols()
{
	// start from start symbol
	// in S -> aBc						S is the start symbol
	//    A -> xBz
	//    B -> c | epsilon

	// from S iterate through its production(s), 
	// if rhs symbol is generating
	//	  add it to the reachable vector

	bool term_present = false;
	bool non_term_present = false;
	bool correct_format = false;
	bool epsilon = false;

	string term;

	reachable_map[START_SYMBOL] = true;

	term = START_SYMBOL;
	for (auto i = ordered_non_terminals.begin(); i != ordered_non_terminals.end(); i++)
	{
		term = *i;

		for (vector<vector<string> >::iterator lhs_rule_set = rule_list.at(term).begin(); lhs_rule_set != rule_list.at(term).end(); ++lhs_rule_set)
		{
			//cout << term << " -> ";
			for (vector<string>::iterator rhs_rule = lhs_rule_set->begin(); rhs_rule != lhs_rule_set->end(); ++rhs_rule)
			{
				contains_non_generating(lhs_rule_set, rhs_rule);

				//cout << "set rule " << *jt << " to useless" << endl;
				//if (*rhs_rule != START_SYMBOL)
					//reachable_map[*rhs_rule] = false;


			}

			term_present = false;
			non_term_present = false;
			correct_format = false;
			epsilon = false;

		}

	}





	reachable_map[START_SYMBOL] = true;
}


// Task 2
void RemoveUselessSymbols()
{
	bool changed = true;


	// step 1 put all symbols, term and non term in vectors, create boolean vector to represent each symbol
	/// initialize_vector_and_map();		

	//print_generating_data(); // for testing

	// step 2, iterate over all terminal, set according vector indexes to true in generating vector, bc terminals generate by default
	set_terminals_to_true();

	//print_generating_data(); // for testing

	// step 3 iterate over all non terminals , if they give epsilon, set the gen map to true for that non term
	set_epsilons_to_true();

	//print_generating_data(); // for testing

	// step 4 iterate through rules, updating the non term's generating map if needed. while changes happen, continue iterating 
	while (changed)
	{
		changed = iterate_through_rules();
	}
	//print_generating_data(); // for testing
	//print_generating_data(); // for testing

	// step 5 iterate through only generating symbols and eliminate non reachable symbols
	determine_reachable_symbols();


}

void initialize_follow_sets()
{
	set<string> followSetVector;

	//  non-terminals
	for (auto i = ordered_non_terminals.begin(); i != ordered_non_terminals.end(); i++)
	{
		follow_set_map[*i] = followSetVector;

	}
	// prints out terminals
	for (auto i = terminals.begin(); i != terminals.end(); i++)
	{

		follow_set_map[*i] = followSetVector;
	}

}

void add_terminals_to_follow_sets()
{

	for (auto i = terminals.begin(); i != terminals.end(); i++)
	{
		follow_set_map[*i].insert(*i);
	}
}

void add_eof_to_follow_set()
{
	follow_set_map[START_SYMBOL].insert("$");
}



void initialize_first_sets()
{
	set<string> firstSetvector;


	//  non-terminals
	for (auto i = ordered_non_terminals.begin(); i != ordered_non_terminals.end(); i++)
	{
		first_set_map[*i] = firstSetvector;

	}
	// prints out terminals
	for (auto i = terminals.begin(); i != terminals.end(); i++)
	{

		first_set_map[*i] = firstSetvector;
	}

}



void add_terminals_to_first_sets()
{

	for (auto i = terminals.begin(); i != terminals.end(); i++)
	{
		first_set_map[*i].insert(*i);
	}
}

void add_epsilon_to_first_sets()
{
	string term;
	bool has_epsilon = false;

	for (int i = 0; i < ordered_non_terminals.size(); i++)
	{
		term = ordered_non_terminals[i];
		for (vector<vector<string> >::iterator it = rule_list.at(term).begin(); it != rule_list.at(term).end(); ++it)
		{
			//it is now a pointer to a vector<int>
			for (vector<string>::iterator jt = it->begin(); jt != it->end(); ++jt)
			{
				if (*jt == "#")
				{
					first_set_map[term].insert("#");
				}
			}
		}
	}
}


void print_first_sets()
{
	string term;
	string symbol;
	vector<string> v;
	int count = 0;


	string result = "";
	bool print = false;



	for (int i = 0; i < ordered_non_terminals.size(); i++)
	{
		term = ordered_non_terminals[i];

		result = "FIRST(" + term + ") = {";
		for (auto i = terminals.begin(); i != terminals.end(); i++)
		{
			symbol = *i;

			for (set<string> ::iterator it = first_set_map.at(term).begin(); it != first_set_map.at(term).end(); ++it)
			{
				if (symbol == *it)
				{
					v.push_back(*it);
					print = true;
					break;
				}
			}
		}

		if (print)
		{
			cout << result;
			for (vector<string>::iterator it = v.begin(); it != v.end(); it++)
			{
				cout << " " << *it;

				if (count < v.size() - 1)
				{
					cout << ",";
				}
				else
				{
					cout << " }";
				}

				count++;
			}

			print = false;
			count = 0;
			v.erase(v.begin(), v.end());
		}
		cout << endl;
	}
}



void print_follow_sets()
{
	string term;
	string symbol;
	vector<string> v;
	int count = 0;


	string result = "";
	bool print = false;
	for (int i = 0; i < ordered_non_terminals.size(); i++)
	{
		term = ordered_non_terminals[i];

		result = "FOLLOW(" + term + ") = {";

		for (auto i = terminals.begin(); i != terminals.end(); i++)
		{
			symbol = *i;

			for (set<string> ::iterator it = follow_set_map.at(term).begin(); it != follow_set_map.at(term).end(); ++it)
			{
				if (symbol == *it)
				{
					v.push_back(*it);
					print = true;
					break;
				}
			}
		}

		if (print)
		{
			cout << result;
			for (vector<string>::iterator it = v.begin(); it != v.end(); it++)
			{
				cout << " " << *it;

				if (count < v.size() - 1)
				{
					cout << ",";
				}
				else
				{
					cout << " }";
				}

				count++;
			}

			print = false;
			count = 0;
			v.erase(v.begin(), v.end());
		}
		cout << endl;
	}
}



bool add_follow_set_by_iteration()
{

	bool change_made = false;
	bool contains_epsilon = false;
	string nonterm;
	string symbol;
	string next_symbol;
	int initialSize = 0, newSize = 0;
	bool is_in, last_symbol = false;
	vector<string>::iterator temp_rule;
	int rule_size = 0;
	int count = 0;

	// for all non terminals
	for (int i = 0; i < ordered_non_terminals.size(); i++)
	{

		nonterm = ordered_non_terminals[i];

		// iterate each non terminal in the rule set
		for (vector<vector<string> >::iterator NON_TERM_RULES = rule_list.at(nonterm).begin(); NON_TERM_RULES != rule_list.at(nonterm).end(); ++NON_TERM_RULES)
		{
			rule_size = NON_TERM_RULES->size();

			// for all rules of each non term
			for (vector<string>::iterator rule = NON_TERM_RULES->begin(); rule != NON_TERM_RULES->end(); ++rule)
			{
				count++;

				if (count == rule_size)
				{
					last_symbol = true;
				}
				else
				{
					temp_rule = rule;
					next_symbol = *(++temp_rule);
				}

				// rule 2
				// A -> a B b

				if (non_term_map[*rule] && (non_term_map[next_symbol] || term_map[next_symbol]) && !last_symbol)
				{

					initialSize = follow_set_map[*rule].size(); // follow(rule)

					// union the follow(rule) set with first(nextsymbol) set 
					auto pos = follow_set_map[*rule].begin(); // follow(rule)
					for (auto it = first_set_map[next_symbol].begin(); it != first_set_map[next_symbol].end(); ++it) { // first(next symbol)
						if (*it != "#")
							pos = follow_set_map[*rule].insert(pos, *it); // follow(rule)
						if (*it == "#")
							contains_epsilon = true;
					}



					newSize = follow_set_map[*rule].size();
				}

				// rule 3
				// A -> aB     follow(B) U follow(A)
				else if (non_term_map[*rule] && last_symbol)
				{
					initialSize = follow_set_map[*rule].size(); // follow(rule)

					// union the follow(rule) set with follow(nextsymbol) set 
					auto pos = follow_set_map[*rule].begin(); // follow(rule)
					for (auto it = follow_set_map[nonterm].begin(); it != follow_set_map[nonterm].end(); ++it) { // follow(nonterm)
						if (*it != "#")
							pos = follow_set_map[*rule].insert(pos, *it); // follow(rule)
						if (*it == "#")
							contains_epsilon = true;
					}

					newSize = follow_set_map[*rule].size();
				}

				// rule 4
				// A -> aBb
				else if (non_term_map[*rule] && non_term_map[next_symbol] && !last_symbol)
				{
					// does it contain epsilon?
					if (first_set_map[next_symbol].count("#")) {
						// epsilon is in the set, count is 1
						contains_epsilon = true;
					}
					else {
						// count zero, i.e. epsilon not in the set
						contains_epsilon = false;
					}

					if (contains_epsilon)
					{
						initialSize = follow_set_map[*rule].size(); // follow(rule)
						// union the follow(rule) set with follow(nonterm) set 
						auto pos = follow_set_map[*rule].begin(); // follow(rule)
						for (auto it = follow_set_map[nonterm].begin(); it != follow_set_map[nonterm].end(); ++it) { // follow(nonterm)
							if (*it != "#")
								pos = follow_set_map[*rule].insert(pos, *it); // follow(rule)
							if (*it == "#")
								change_made = true;
						}

						newSize = follow_set_map[*rule].size();
					}
					else
					{
						initialSize = follow_set_map[*rule].size(); // follow(rule)
						// union the follow(rule) set with follow(nonterm) set 
						auto pos = follow_set_map[*rule].begin(); // follow(rule)
						for (auto it = first_set_map[next_symbol].begin(); it != first_set_map[next_symbol].end(); ++it) { // follow(nonterm)
							if (*it != "#")
								pos = follow_set_map[*rule].insert(pos, *it); // follow(rule)
							if (*it == "#")
								change_made = true;
						}

						newSize = follow_set_map[*rule].size();
					}
				}

				// if the size of the set changed 
				//  change made = true
				if (newSize != initialSize)
				{
					change_made = true;
				}
			}
			rule_size = 0;
			count = 0;
			last_symbol = false;
			vector<string>::iterator temp_rule;

		}
	}

	return change_made;
}



bool add_first_set_by_iteration()
{
	bool change_made = false;
	bool contains_epsilon = false;
	string nonterm;
	string symbol;
	int initialSize = 0, newSize = 0;
	//bool is_in;


	// for all non terminals
	for (int i = 0; i < ordered_non_terminals.size(); i++)
	{
		nonterm = ordered_non_terminals[i];

		// iterate each non terminal in the rule set
		for (vector<vector<string> >::iterator NON_TERM_RULES = rule_list.at(nonterm).begin(); NON_TERM_RULES != rule_list.at(nonterm).end(); ++NON_TERM_RULES)
		{
			// for all rules of each non term
			for (vector<string>::iterator rule = NON_TERM_RULES->begin(); rule != NON_TERM_RULES->end(); ++rule)
			{
				// if the rule is a terminal
				if (term_map[*rule])
				{
					initialSize = first_set_map[nonterm].size();

					// union the first(rule) set with first(nonterm) set 
					auto pos = first_set_map[nonterm].begin();
					for (auto it = first_set_map[*rule].begin(); it != first_set_map[*rule].end(); ++it) {
						pos = first_set_map[nonterm].insert(pos, *it);
					}

					newSize = first_set_map[nonterm].size();

					// if the size of the set changed 
					//  made = true
					if (newSize != initialSize)
					{
						change_made = true;
					}
					break;

				}
				// else if rule is a non terminal
				else if (non_term_map[*rule])
				{

					// INITIAL CHECK FOR EPSILON IN THAT FIRST SET
					// does it contain epsilon?
					if (first_set_map[*rule].count("#")) {
						// epsilon is in the set, count is 1
						contains_epsilon = true;
					}
					else {
						// count zero, i.e. epsilon not in the set
						contains_epsilon = false;
					}


					// union the first(rule) set with first(nonterm) set 
					initialSize = first_set_map[nonterm].size();

					// union the two first sets - epsilon
					auto pos = first_set_map[nonterm].begin();
					for (auto it = first_set_map[*rule].begin(); it != first_set_map[*rule].end(); ++it) {
						if (*it != "#")
							pos = first_set_map[nonterm].insert(pos, *it);
						if (*it == "#")
							contains_epsilon = true;
					}


					if (contains_epsilon && rule == --NON_TERM_RULES->end())
					{
						first_set_map[nonterm].insert("#");
					}

					// check new size
					newSize = first_set_map[nonterm].size();

					// if the size of the set changed 
					//  change made = true
					if (newSize != initialSize)
					{
						change_made = true;
					}

					if (!contains_epsilon) break;


					// if CONTAINS epsilon

						// append first(rule) to first(nonterm)
						// change made = true
						// check next rule, do not breaK

				}


			}

		}
		contains_epsilon = false;
	}

	return change_made;
}


// Task 3
void CalculateFirstSets()
{
	// step 1 if x is terminal, then first(x) = {x}
	initialize_first_sets();
	add_terminals_to_first_sets();
	//print_first_sets();

	add_epsilon_to_first_sets();

	while (add_first_set_by_iteration());


	///cout << "\n\n";
	first_set_calculated = true;
	terminals.push_back("$");

}

// Task 4
void CalculateFollowSets()
{
	//cout << "4\n";
	//cout << "CalculateFollowSets";
	initialize_follow_sets();
	add_terminals_to_follow_sets();
	add_eof_to_follow_set();



	while (add_follow_set_by_iteration());

	


}

// Task 5
void CheckIfGrammarHasPredictiveParser()
{
	//cout << "5\n";
	//cout << "CheckIfGrammarHasPredictiveParser";
	RemoveUselessSymbols();

	string non_terminal;
	for (int i = 0; i < ordered_non_terminals.size(); i++)
	{
		non_terminal = ordered_non_terminals[i];

		if (generating_map[non_terminal] == false) 
		{
			contains_useless_symbols = true;
			break;
		}

	}

	if (contains_useless_symbols) 
	{
		cout << "NO" << endl; // no predictive parser
	}
	else 
	{
		cout << "YES" << endl; // yes, predictive parser
	}

}

int main(int argc, char* argv[])
{
	int task;

	/*
	commented out to manually add input for testing
	if (argc < 2)
	{
		cout << "Error: missing argument\n";
		return 1;
	}
	*/

	/*
	   Note that by convention argv[0] is the name of your executable,
	   and the first argument to your program is stored in argv[1]
	 */

	 //task = atoi(argv[1]);

	ReadGrammar();  // Reads the input grammar from standard input
					// and represents it internally in data structures
					// as described in project 2 presentation file
	orderSymbols();
	initialize_vector_and_map();


	//printf("\nenter a task: ");
	scanf_s("%d", &task); ///// added for testing

	while (task != 0)
	{
		switch (task) {
		case 1: printTerminalsAndNonTerminals();
			break;

		case 2:
			RemoveUselessSymbols();
			print_useful_only();

			break;

		case 3: 

			if (!first_set_calculated) 
			{
				CalculateFirstSets();
			}
			print_first_sets();
			break;

		case 4: // follow set
			if (first_set_calculated)
			{
				CalculateFollowSets();
			}
			else 
			{
				CalculateFirstSets();
				CalculateFollowSets();
			}
			print_follow_sets();
			break;

		case 5: CheckIfGrammarHasPredictiveParser();
			break;
		case 7:
			printmap();
			break;
		default:
			cout << "Error: unrecognized task number " << task << "\n";
			break;
		}

		///printf("\nenter a task: ");
		scanf_s("%d", &task); ///// added for testing
	}
	return 0;
}