#include "analysis/compiler.hpp"
#include "analysis/main_parser/algsynLexer.h"
#include "analysis/main_parser/algsynParser.h"
#include "analysis/extractor/extractorLexer.h"
#include "analysis/extractor/extractorParser.h"
#include "analysis/extractor/extractorBaseListener.h"
#include "analysis/main_parser/algsynBaseListener.h"
#include "analysis/single/single_lex_wrapper.hpp"
#include <memory>
#include <algorithm>
#include "string_ops.hpp"
#include "language.hpp"

class MainErrorListener : public antlr4::BaseErrorListener {
public:
	MainErrorListener() : antlr4::BaseErrorListener(), has_error(false) {}
	virtual void syntaxError(
		antlr4::Recognizer* recognizer,
		antlr4::Token* errorSymbol,
		size_t line, size_t cpos,
		const std::string& msg,
		std::exception_ptr e) override
	{
		std::string cpy = msg;
		if (msg.find(';') == std::string::npos)
			ReplaceAll(cpy, "'<EOF>'", "at the end of the line.");
		else 
			ReplaceAll(cpy, "'<EOF>'", "the end of the line.");

		ReplaceAll(cpy, "LITERAL", "0, 1");
		ReplaceAll(cpy, "ID", "variable");
		error_list.emplace_back(std::max(unsigned int(errorSymbol->getLine() - 1u), 1u), cpy);
		has_error = true;
	}
	bool HasGrammarError() { return has_error; }
	std::vector<SyntaxError>& GetErrorList() { return error_list; }
private:
	bool has_error;
	std::vector<SyntaxError> error_list;
};


class Extractor : public extractorBaseListener {

public:
	Extractor() : extractorBaseListener(), has_error(false), mem_stmt_prec(false), inp_stmt_prec(false) {}
	void Reset() { mem_args.clear(); inp_args.clear(); outs.clear(); non_outs.clear(); }

	CircuitDescriptor GenerateResult() {

		CircuitDescriptor desc;

		FindIDs();
		ResolveImplicitMultiplications();

		FindInlineInputDecl();
		FindInlineMemDecl();

		has_error = !CheckInpDeclValidity();
		has_error |= !CheckMemDeclValidity();

		CheckIDsForKeywords();

		if (outs.empty() && mem_args.empty()) {
			has_error = true;
			error_list.emplace_back(0, "You must declare at least one output expression.");
		}

		if (inp_args.empty()) {
			has_error = true;
			error_list.emplace_back(0, "There has to be at least one input variable.");
		}

		if (!has_error) {

			for (const auto& i : inp_args) {
				desc.SubmitInputVariable(i);
			}

			for (const auto& m : mem_args) {
				desc.SubmitStateVariable(m);
			}

			if (name.empty()) name = "Circuit";
			
			for (const auto& [id, expr] : non_outs)
			{
				std::string modified_expr = SurroundIDs(expr);
				modified_expr = ReplaceIDs(id, modified_expr);
				non_outs[id] = modified_expr;
			}

			ankerl::unordered_dense::set<std::string> refs;
			for (auto&[id,expr] : outs)
			{
				refs.clear();
				std::string modified_expr = SurroundIDs(expr);
				modified_expr = ReplaceIDs(id, modified_expr);
				expr = modified_expr;
			}

			RemoveInputsFromIDList();

			for (auto& [id, expr] : outs) {
				FindReferences(id, expr, refs);

				if (IsUpdateEquation(id, expr)) {
					desc.SubmitEquation(EquationType::Update, id, expr, refs);
				}
				else {
					desc.SubmitEquation(EquationType::Output, id, expr, refs);
					desc.SubmitOutputVariable(id);
				}
			}

			desc.SetCategory(category);
			desc.SetName(name);
			desc.SetType(FindType());

			desc.Finalize();
			/*struct {
				bool operator()(const Instruction& l, const Instruction& r) { return l.type < r.type; }
			} instr_sort_fnctr;

			std::sort(result.begin(), result.end(), instr_sort_fnctr);*/

		}
		
		return desc;
	}

	bool HasError() const { return has_error; }
	std::vector<SyntaxError>& GetErrorList() { return error_list; }

private:
	ankerl::unordered_dense::set<std::string> mem_args, inp_args, all_ids;
	ankerl::unordered_dense::map<std::string, std::string> outs, non_outs;
	
	ankerl::unordered_dense::set<std::string> inline_mem_decl, inline_inp_decl;
	std::vector<SyntaxError> error_list;
	std::vector<std::string> sorted_id_list;
	std::string name, category;
	
	bool has_error;
	bool mem_stmt_prec, inp_stmt_prec;

	void FindInlineMemDecl() {
		SLexWrapper slex;

		for (const auto& [id, expr] : outs) {
			auto tokens = slex.GetTokens(expr);

			for (const auto& token : tokens) {
				if (token.type == STOK_ID) {
					if (token.text == id) {
						inline_mem_decl.insert(id);
					} 
				}
			}
		}
		/*
		* Non outing update equations are unsupported
		* 
		for (const auto& [id, expr] : non_outs) {
			if (expr.find(id) != std::string::npos) {
				inline_mem_decl.insert(id);
			}
		}*/
	}

	CircuitType FindType() {
		if (!inline_mem_decl.empty()) return CircuitType::Explicit_Sequential;
		SLexWrapper slex;

		for (const auto& [id, expr] : outs) {
			auto tokens = slex.GetTokens(expr);
			for (const auto& token : tokens) {
				if (token.type == STOK_ID && all_ids.count(token.text) > 0) {
					return CircuitType::Implitcit_Sequential;
				}
			}
		}
		return CircuitType::Combinational;
	}

	void CheckIDsForKeywords() {
		auto& keywords = LangDef::get().GetKeywords();
		for (const auto& id : all_ids) {
			if (keywords.count(id) > 0) {
				has_error = true;
				error_list.emplace_back(0, "Keywords cannot be used as identifiers");
			}
		}
	}

	void ResolveImplicitMultiplications() {
		SLexWrapper slex;
		for (auto& [id, expr] : non_outs) {
			auto tokens = slex.GetTokens(expr);
			for (size_t i = 0; i < tokens.size() - 1; ++i) {
				if (!all_ids.contains(tokens[i].text) && tokens[i].text.length() > 1 && tokens[i].type == STOK_ID) {
					std::string str;
					for (const auto c : tokens[i].text) {
						str += c;
						str += '*';
					}
					str.erase(str.length() - 1);
					expr.replace(tokens[i].cpos, tokens[i].text.length(), str);
					tokens = slex.GetTokens(expr);
					i += tokens[i].text.length() - 1;
				}
			}
		}

		for (auto& [id, expr] : outs) {
			auto tokens = slex.GetTokens(expr);
			for (size_t i = 0; i < tokens.size() - 1; ++i) {
				if (!all_ids.contains(tokens[i].text) && tokens[i].text.length() > 1 && tokens[i].type == STOK_ID) {
					std::string str;
					for (const auto c : tokens[i].text) {
						str += c;
						str += '*';
					}
					str.erase(str.length() - 1);
					expr.replace(tokens[i].cpos, tokens[i].text.length(), str);
					i += tokens[i].text.length() - 1;
					tokens = slex.GetTokens(expr);
				}
			}
		}
	}

	void RemoveInputsFromIDList() {
		auto inputs_functor = [this](const std::string& id) -> bool {
				return inp_args.count(id) > 0;
			};
		std::erase_if(all_ids, inputs_functor);
	}

	void FindReferences(const std::string& id, const std::string& expr, ankerl::unordered_dense::set<std::string>& refs) {
		SLexWrapper slex;
		auto tkns = slex.GetTokens(expr);
		for (const auto& tkn : tkns) {
			if (all_ids.count(tkn.text) > 0 && refs.count(tkn.text) == 0) {
				refs.insert(tkn.text);
			}
		}
	}

	void FindIDs() {
		all_ids.clear();
		for (const auto& [id, expr] : outs) {
			all_ids.insert(id);
		}
		for (const auto& [id, expr] : non_outs) {
			all_ids.insert(id);
		}

		if (mem_stmt_prec) {
			for (const auto& mem_id : mem_args)
				all_ids.insert(mem_id);
		}
		if (inp_stmt_prec) {
			for (const auto& inp_id : inp_args)
				all_ids.insert(inp_id);
		}
	
		struct {
			bool operator()(const std::string& l, const std::string& r) { return l.length() > r.length(); }
		} id_sort_fnctr;

		sorted_id_list = std::vector<std::string>(all_ids.begin(), all_ids.end());
		std::sort(sorted_id_list.begin(), sorted_id_list.end(), id_sort_fnctr);
	}

	void FindInlineInputDecl() {
		std::string exprs;
		all_ids.clear();
		for (const auto& [id, expr] : outs) {
			exprs += std::format("({})",expr);
			all_ids.insert(id);
		}
		for (const auto& [id, expr] : non_outs) {
			exprs += std::format("({})", expr);
			all_ids.insert(id);
		}
		if (mem_stmt_prec) {
			for (const auto& mem_id : mem_args)
				all_ids.insert(mem_id);
		}
		if (inp_stmt_prec) {
			for (const auto& inp_id : inp_args)
				all_ids.insert(inp_id);
		}
		SLexWrapper slex;
		auto tokens = slex.GetTokens(exprs);

		for (const auto& id : all_ids) {
			auto pred = [&](const SToken& item) -> bool { 
					return item.text == id;
				};

			tokens.erase(std::remove_if(tokens.begin(), tokens.end(), pred), tokens.end());
		}

		exprs.clear();

		for (const auto& token : tokens) {
			if(token.type == STOK_ID)
				exprs += token.text;
		}

		for (const char c : exprs)
		{
			if (std::isalpha(c)) {
				inline_inp_decl.insert(std::string(1, c));
				//all_ids.insert(std::string(1, c));
			}
		}

		struct {
			bool operator()(const std::string& l, const std::string& r) { return l.length() > r.length(); }
		} id_sort_fnctr;

		sorted_id_list = std::vector<std::string>(all_ids.begin(), all_ids.end());
		std::sort(sorted_id_list.begin(), sorted_id_list.end(), id_sort_fnctr);
	}

	bool CheckMemDeclValidity() {
		if (mem_stmt_prec) {
			for (const auto& imid : inline_mem_decl) {
				if (mem_args.find(imid) == mem_args.end()) {
					error_list.emplace_back(0, std::format("Use of undefined variable '{}'.", imid));
					return false;
				}
			}
			return true;
		}
		else {
			if (inline_mem_decl.size() > 8) {
				error_list.emplace_back(0, "Too many memory declarations.");
				return false;
			}
			mem_args = inline_mem_decl;
			return true;
		}
	}

	bool CheckInpDeclValidity() {
		if (inp_stmt_prec) {
			for (const auto& iid : inline_inp_decl) {
				if (inp_args.find(iid) == inp_args.end()) {
					error_list.emplace_back(0, std::format("Use of undefined variable '{}'.", iid));
					return false;
				}
			}
			return true;
		}
		else {
			if (inline_inp_decl.size() > 8) {
				error_list.emplace_back(0, "Too many input variables.");
				return false;
			}
			inp_args = inline_inp_decl;
			return true;
		}
	}
	
	std::string SurroundIDs(const std::string& input)
	{
		std::string result = input;

		SLexWrapper slex;
		auto tokens = slex.GetTokens(result);
		for (const std::string& keyword : sorted_id_list) {

			for (size_t i = 0; i < tokens.size(); ++i) {
				if (tokens[i].type == STOK_ID) {
					if (tokens[i].text == keyword) {
						SurroundWith(result, tokens[i].cpos, keyword.length());
						tokens = slex.GetTokens(result);
						++i;
					}
				}
			}
		}

		return result;
	}

	inline bool IsUpdateEquation(const std::string& id, const std::string& expr) {
		SLexWrapper slex;
		auto tokens = slex.GetTokens(expr);

		for (const auto& token : tokens) {
			if (token.type == STOK_ID) {
				if (token.text == id) {
					return true;
				}
			}
		}

		return false;
	}

	inline std::string ReplaceIDs(const std::string& repl_id, const std::string& expr) {
		std::string result = expr;
		SLexWrapper slex;
		auto tokens = slex.GetTokens(result);
		
		for (const auto& [id, expr] : non_outs) {
			for (size_t i = 0; i < tokens.size(); ++i) {
				if (tokens[i].type == STOK_ID) {
					if (tokens[i].text == id) {
						result.replace(tokens[i].cpos, id.length(), expr);
						tokens = slex.GetTokens(result);
						++i;
					}
				}
			}
		}
		return result;
	}

	inline std::string ReplaceIntermediates(const std::string& expr) {
		std::string result = expr;
		for (const auto& [id, exp] : non_outs) {
			std::string from = std::format("({})", id);
			std::string to = std::format("({})", exp);
			ReplaceAll(result, from, to);
		}
		return result;
	}

	virtual void enterName(extractorParser::NameContext* ctx) override { 
		if(name.empty())
			name = ctx->ID()->getText();
		else {
			has_error = true;
			error_list.emplace_back(ctx->ID()->getSymbol()->getLine(), "Multiple name tags.");
		}
	}

	virtual void enterMem(extractorParser::MemContext* ctx) override { 
		extractorParser::Arg_blockContext* args = ctx->arg_block();
		if (args != nullptr && !mem_stmt_prec) {
			mem_stmt_prec = true;
			for (antlr4::tree::TerminalNode* idNode : args->ID()) {
				std::string id = idNode->getText();
				mem_args.insert(id);
			}
		}
	}

	virtual void enterInp(extractorParser::InpContext* ctx) override { 
		extractorParser::Arg_blockContext* args = ctx->arg_block();
		if (args != nullptr && !inp_stmt_prec) {
			inp_stmt_prec = true;
			for (antlr4::tree::TerminalNode* idNode : args->ID()) {
				std::string id = idNode->getText();
				inp_args.insert(id);
			}
		}
	}

	virtual void enterNon_outing(extractorParser::Non_outingContext* ctx) override {
		auto id = ctx->ID()->getText();
		if (ctx->expr_block()->EXPR() != nullptr) {

			auto expr = ctx->expr_block()->EXPR()->getText();
			RemoveSpaces(id);
			RemoveSpaces(expr);
			RemoveChar(expr, '=');
			RemoveChar(expr, ';');
			if (IsUpdateEquation(id, expr)) {
				has_error = true;
				error_list.emplace_back(ctx->ID()->getSymbol()->getLine(), "Update equations cannot be declared as intermidiate equations");
			}
			non_outs.insert(std::pair<std::string, std::string>(id, expr));
		
		}
	}

	virtual void enterOuting(extractorParser::OutingContext* ctx) override { 
		auto id = ctx->ID()->getText();
		if (ctx->expr_block()->EXPR() != nullptr) {

			auto expr = ctx->expr_block()->EXPR()->getText();
			RemoveSpaces(id);
			RemoveSpaces(expr);
			RemoveChar(expr, '=');
			RemoveChar(expr, ';');

			outs.insert(std::pair<std::string, std::string>(id, expr));
		}
	}

	virtual void enterCategory(extractorParser::CategoryContext* ctx) override { 
		if (ctx->ID() != nullptr) {
			auto type = ctx->ID()->getText();
			category = type;
		}
	}
};

class SyntaxCheckListener : public algsynBaseListener {
public:
	SyntaxCheckListener() : algsynBaseListener() {}
	bool HasSyntaxError() { return has_error; }
	std::vector<SyntaxError>& GetErrorList() { return error_list; }

private:
	bool has_error = false, has_mem_decl = false, has_inp_decl = false,
		has_name = false, has_category = false;
	std::unordered_set<std::string> check_set, outs;
	std::vector<SyntaxError> error_list;

	virtual void enterName_decl(algsynParser::Name_declContext* ctx) override {
		if (has_name) {
			has_error = true;
			error_list.emplace_back(ctx->ID()->getSymbol()->getLine(), "Multiple name tags.");
		}
		has_name = true;
	}

	virtual void enterInp_decl(algsynParser::Inp_declContext* ctx) override {
		algsynParser::ArgsContext* args = ctx->args();
		//check_set.clear();

		if (has_inp_decl) {
			has_error = true;
			error_list.emplace_back(
				args->ID()[0]->getSymbol()->getLine(),
				"More than one input statements found"
			);
			return;
		}

		if (args != nullptr) {

			if(args->ID().size() > 8){
				has_error = true;
				error_list.emplace_back(
					args->ID()[0]->getSymbol()->getLine(),
					"Too many input declarations. (Max 8)");
				return;
			}

			for (antlr4::tree::TerminalNode* idNode : args->ID()) {
				std::string id = idNode->getText();
				if (check_set.count(id) == 0)
					check_set.insert(id);
				else {
					has_error = true;
					error_list.emplace_back(
						idNode->getSymbol()->getLine(),
						std::format("Redefinition of input variable '{}'", id));
				}
					
			}

			has_inp_decl = true;
		}
	}

	virtual void enterMem_decl(algsynParser::Mem_declContext* ctx) override { 
		algsynParser::ArgsContext* args = ctx->args();
		//check_set.clear();
		
		if (args != nullptr) {

			if (has_mem_decl) {
				has_error = true;
				error_list.emplace_back(
					args->ID()[0]->getSymbol()->getLine(),
					"More than one memory statements found");
				return;
			}

			if (args->ID().size() > 8) {
				has_error = true;
				error_list.emplace_back(
					args->ID()[0]->getSymbol()->getLine(),
					"Too many memory declarations. (Max 8)");
			}

			for (antlr4::tree::TerminalNode* idNode : args->ID()) {
				std::string id = idNode->getText();
				if (check_set.count(id) == 0)
					check_set.insert(id);
				else {
					has_error = true;
					error_list.emplace_back(
						idNode->getSymbol()->getLine(),
						std::format("Redefinition of memory element '{}'", id));
				}

			}

			has_mem_decl = true;
		}
	}

	virtual void enterOuting(algsynParser::OutingContext* ctx) override { 
		auto id = ctx->ID()->getText();
		if (outs.count(id) == 0) {
			outs.insert(id);
		}
		else {
			has_error = true;
			error_list.emplace_back(
				ctx->ID()->getSymbol()->getLine(),
				std::format("Redefinition of output variable '{}'", id));
		}
	}

	virtual void enterNon_outing(algsynParser::Non_outingContext* ctx) override { 
		auto id = ctx->ID()->getText();
		if (outs.count(id) == 0) {
			outs.insert(id);
		}
		else {
			has_error = true;
			error_list.emplace_back(
				ctx->ID()->getSymbol()->getLine(),
				std::format("Redefinition of output variable '{}'", id));
		}
	}

	virtual void enterCategory_decl(algsynParser::Category_declContext* ctx) override {
		if (has_category) {
			has_error = true;
			error_list.emplace_back(0, "Multiple category type declarations");
		}
		else {
			has_category = true;
		}
	}
};

Compiler::Compiler()
{
}

bool Compiler::Compile(const std::string& input)
{
	bool no_errors = CheckSyntax(input);

	if (!no_errors) return false;

	// Proceed with compilation if there are no errors

	antlr4::ANTLRInputStream extr_istr(input);
	extractorLexer extr_lex(&extr_istr);
	antlr4::CommonTokenStream extr_tokens(&extr_lex);
	extractorParser extr_parser(&extr_tokens);

	extractorParser::ProgramContext* extr_tree = extr_parser.program();
	
	std::unique_ptr<Extractor> input_processor = std::make_unique<Extractor>();
	antlr4::tree::ParseTreeWalker::DEFAULT.walk(input_processor.get(), extr_tree);

	last_result = input_processor->GenerateResult();

	// Return false if there are declaration errors
	if (input_processor->HasError())
	{
		error_list.insert(error_list.end(), input_processor->GetErrorList().begin(), input_processor->GetErrorList().end());
		return false;
	}

	return true;
}

bool Compiler::CheckSyntax(const std::string& input)
{
	error_list.clear();

	antlr4::ANTLRInputStream istr(input);
	algsynLexer lexer(&istr);
	antlr4::CommonTokenStream tokens(&lexer);
	algsynParser parser(&tokens);

	MainErrorListener err_listner;

	lexer.removeErrorListeners();
	lexer.addErrorListener(&err_listner);

	parser.removeErrorListeners();
	parser.addErrorListener(&err_listner);

	algsynParser::ProgramContext* tree = parser.program();

	// Return false if grammar has error
	if (err_listner.HasGrammarError())
	{
		error_list.insert(error_list.end(), err_listner.GetErrorList().begin(), err_listner.GetErrorList().end());
		return false;
	}

	SyntaxCheckListener syntax_checker;
	antlr4::tree::ParseTreeWalker::DEFAULT.walk(&syntax_checker, tree);

	// Return false if there are errors in definitions
	if (syntax_checker.HasSyntaxError()) {
		error_list.insert(error_list.end(), syntax_checker.GetErrorList().begin(), syntax_checker.GetErrorList().end());
		return false;
	}

	return true;
}

bool Compiler::QuickCompile(const std::string& input) {
	antlr4::ANTLRInputStream extr_istr(input);
	extractorLexer extr_lex(&extr_istr);
	antlr4::CommonTokenStream extr_tokens(&extr_lex);
	extractorParser extr_parser(&extr_tokens);

	extractorParser::ProgramContext* extr_tree = extr_parser.program();

	std::unique_ptr<Extractor> input_processor = std::make_unique<Extractor>();
	antlr4::tree::ParseTreeWalker::DEFAULT.walk(input_processor.get(), extr_tree);

	last_result = input_processor->GenerateResult();

	return true;
}