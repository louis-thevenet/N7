// Generated from MiniCParser.g4 by ANTLR 4.13.1

package fr.n7.stl.minic.parser;
import java.io.IOException;
import java.io.File;
import java.io.FileInputStream;
import java.io.PrintWriter;
import java.io.IOException;
import fr.n7.stl.minic.ast.*;
import fr.n7.stl.minic.ast.expression.*;
import fr.n7.stl.minic.ast.expression.accessible.*;
import fr.n7.stl.minic.ast.expression.allocation.*;
import fr.n7.stl.minic.ast.expression.assignable.*;
import fr.n7.stl.minic.ast.expression.value.*;
import fr.n7.stl.minic.ast.instruction.*;
import fr.n7.stl.minic.ast.instruction.declaration.*;
import fr.n7.stl.minic.ast.scope.*;
import fr.n7.stl.minic.ast.type.*;
import fr.n7.stl.minic.ast.type.declaration.*;
import fr.n7.stl.util.*;
import fr.n7.stl.tam.ast.*;
import fr.n7.stl.tam.ast.impl.*;

import org.antlr.v4.runtime.tree.ParseTreeListener;

/**
 * This interface defines a complete listener for a parse tree produced by
 * {@link MiniCParser}.
 */
public interface MiniCParserListener extends ParseTreeListener {
	/**
	 * Enter a parse tree produced by {@link MiniCParser#programme}.
	 * @param ctx the parse tree
	 */
	void enterProgramme(MiniCParser.ProgrammeContext ctx);
	/**
	 * Exit a parse tree produced by {@link MiniCParser#programme}.
	 * @param ctx the parse tree
	 */
	void exitProgramme(MiniCParser.ProgrammeContext ctx);
	/**
	 * Enter a parse tree produced by {@link MiniCParser#bloc}.
	 * @param ctx the parse tree
	 */
	void enterBloc(MiniCParser.BlocContext ctx);
	/**
	 * Exit a parse tree produced by {@link MiniCParser#bloc}.
	 * @param ctx the parse tree
	 */
	void exitBloc(MiniCParser.BlocContext ctx);
	/**
	 * Enter a parse tree produced by {@link MiniCParser#parametres}.
	 * @param ctx the parse tree
	 */
	void enterParametres(MiniCParser.ParametresContext ctx);
	/**
	 * Exit a parse tree produced by {@link MiniCParser#parametres}.
	 * @param ctx the parse tree
	 */
	void exitParametres(MiniCParser.ParametresContext ctx);
	/**
	 * Enter a parse tree produced by the {@code instructionDeclaration}
	 * labeled alternative in {@link MiniCParser#instruction}.
	 * @param ctx the parse tree
	 */
	void enterInstructionDeclaration(MiniCParser.InstructionDeclarationContext ctx);
	/**
	 * Exit a parse tree produced by the {@code instructionDeclaration}
	 * labeled alternative in {@link MiniCParser#instruction}.
	 * @param ctx the parse tree
	 */
	void exitInstructionDeclaration(MiniCParser.InstructionDeclarationContext ctx);
	/**
	 * Enter a parse tree produced by the {@code instructionTypeDeclaration}
	 * labeled alternative in {@link MiniCParser#instruction}.
	 * @param ctx the parse tree
	 */
	void enterInstructionTypeDeclaration(MiniCParser.InstructionTypeDeclarationContext ctx);
	/**
	 * Exit a parse tree produced by the {@code instructionTypeDeclaration}
	 * labeled alternative in {@link MiniCParser#instruction}.
	 * @param ctx the parse tree
	 */
	void exitInstructionTypeDeclaration(MiniCParser.InstructionTypeDeclarationContext ctx);
	/**
	 * Enter a parse tree produced by the {@code instructionFunctionDeclaration}
	 * labeled alternative in {@link MiniCParser#instruction}.
	 * @param ctx the parse tree
	 */
	void enterInstructionFunctionDeclaration(MiniCParser.InstructionFunctionDeclarationContext ctx);
	/**
	 * Exit a parse tree produced by the {@code instructionFunctionDeclaration}
	 * labeled alternative in {@link MiniCParser#instruction}.
	 * @param ctx the parse tree
	 */
	void exitInstructionFunctionDeclaration(MiniCParser.InstructionFunctionDeclarationContext ctx);
	/**
	 * Enter a parse tree produced by the {@code instructionAffectation}
	 * labeled alternative in {@link MiniCParser#instruction}.
	 * @param ctx the parse tree
	 */
	void enterInstructionAffectation(MiniCParser.InstructionAffectationContext ctx);
	/**
	 * Exit a parse tree produced by the {@code instructionAffectation}
	 * labeled alternative in {@link MiniCParser#instruction}.
	 * @param ctx the parse tree
	 */
	void exitInstructionAffectation(MiniCParser.InstructionAffectationContext ctx);
	/**
	 * Enter a parse tree produced by the {@code instructionAffichage}
	 * labeled alternative in {@link MiniCParser#instruction}.
	 * @param ctx the parse tree
	 */
	void enterInstructionAffichage(MiniCParser.InstructionAffichageContext ctx);
	/**
	 * Exit a parse tree produced by the {@code instructionAffichage}
	 * labeled alternative in {@link MiniCParser#instruction}.
	 * @param ctx the parse tree
	 */
	void exitInstructionAffichage(MiniCParser.InstructionAffichageContext ctx);
	/**
	 * Enter a parse tree produced by the {@code instructionSi}
	 * labeled alternative in {@link MiniCParser#instruction}.
	 * @param ctx the parse tree
	 */
	void enterInstructionSi(MiniCParser.InstructionSiContext ctx);
	/**
	 * Exit a parse tree produced by the {@code instructionSi}
	 * labeled alternative in {@link MiniCParser#instruction}.
	 * @param ctx the parse tree
	 */
	void exitInstructionSi(MiniCParser.InstructionSiContext ctx);
	/**
	 * Enter a parse tree produced by the {@code instructionSiSinon}
	 * labeled alternative in {@link MiniCParser#instruction}.
	 * @param ctx the parse tree
	 */
	void enterInstructionSiSinon(MiniCParser.InstructionSiSinonContext ctx);
	/**
	 * Exit a parse tree produced by the {@code instructionSiSinon}
	 * labeled alternative in {@link MiniCParser#instruction}.
	 * @param ctx the parse tree
	 */
	void exitInstructionSiSinon(MiniCParser.InstructionSiSinonContext ctx);
	/**
	 * Enter a parse tree produced by the {@code instructionReturn}
	 * labeled alternative in {@link MiniCParser#instruction}.
	 * @param ctx the parse tree
	 */
	void enterInstructionReturn(MiniCParser.InstructionReturnContext ctx);
	/**
	 * Exit a parse tree produced by the {@code instructionReturn}
	 * labeled alternative in {@link MiniCParser#instruction}.
	 * @param ctx the parse tree
	 */
	void exitInstructionReturn(MiniCParser.InstructionReturnContext ctx);
	/**
	 * Enter a parse tree produced by the {@code instructionTantQue}
	 * labeled alternative in {@link MiniCParser#instruction}.
	 * @param ctx the parse tree
	 */
	void enterInstructionTantQue(MiniCParser.InstructionTantQueContext ctx);
	/**
	 * Exit a parse tree produced by the {@code instructionTantQue}
	 * labeled alternative in {@link MiniCParser#instruction}.
	 * @param ctx the parse tree
	 */
	void exitInstructionTantQue(MiniCParser.InstructionTantQueContext ctx);
	/**
	 * Enter a parse tree produced by {@link MiniCParser#atomique}.
	 * @param ctx the parse tree
	 */
	void enterAtomique(MiniCParser.AtomiqueContext ctx);
	/**
	 * Exit a parse tree produced by {@link MiniCParser#atomique}.
	 * @param ctx the parse tree
	 */
	void exitAtomique(MiniCParser.AtomiqueContext ctx);
	/**
	 * Enter a parse tree produced by {@link MiniCParser#champ}.
	 * @param ctx the parse tree
	 */
	void enterChamp(MiniCParser.ChampContext ctx);
	/**
	 * Exit a parse tree produced by {@link MiniCParser#champ}.
	 * @param ctx the parse tree
	 */
	void exitChamp(MiniCParser.ChampContext ctx);
	/**
	 * Enter a parse tree produced by {@link MiniCParser#etiquettes}.
	 * @param ctx the parse tree
	 */
	void enterEtiquettes(MiniCParser.EtiquettesContext ctx);
	/**
	 * Exit a parse tree produced by {@link MiniCParser#etiquettes}.
	 * @param ctx the parse tree
	 */
	void exitEtiquettes(MiniCParser.EtiquettesContext ctx);
	/**
	 * Enter a parse tree produced by the {@code typeAtomic}
	 * labeled alternative in {@link MiniCParser#type}.
	 * @param ctx the parse tree
	 */
	void enterTypeAtomic(MiniCParser.TypeAtomicContext ctx);
	/**
	 * Exit a parse tree produced by the {@code typeAtomic}
	 * labeled alternative in {@link MiniCParser#type}.
	 * @param ctx the parse tree
	 */
	void exitTypeAtomic(MiniCParser.TypeAtomicContext ctx);
	/**
	 * Enter a parse tree produced by the {@code typeNamed}
	 * labeled alternative in {@link MiniCParser#type}.
	 * @param ctx the parse tree
	 */
	void enterTypeNamed(MiniCParser.TypeNamedContext ctx);
	/**
	 * Exit a parse tree produced by the {@code typeNamed}
	 * labeled alternative in {@link MiniCParser#type}.
	 * @param ctx the parse tree
	 */
	void exitTypeNamed(MiniCParser.TypeNamedContext ctx);
	/**
	 * Enter a parse tree produced by the {@code typeCouple}
	 * labeled alternative in {@link MiniCParser#type}.
	 * @param ctx the parse tree
	 */
	void enterTypeCouple(MiniCParser.TypeCoupleContext ctx);
	/**
	 * Exit a parse tree produced by the {@code typeCouple}
	 * labeled alternative in {@link MiniCParser#type}.
	 * @param ctx the parse tree
	 */
	void exitTypeCouple(MiniCParser.TypeCoupleContext ctx);
	/**
	 * Enter a parse tree produced by the {@code typeRecord}
	 * labeled alternative in {@link MiniCParser#type}.
	 * @param ctx the parse tree
	 */
	void enterTypeRecord(MiniCParser.TypeRecordContext ctx);
	/**
	 * Exit a parse tree produced by the {@code typeRecord}
	 * labeled alternative in {@link MiniCParser#type}.
	 * @param ctx the parse tree
	 */
	void exitTypeRecord(MiniCParser.TypeRecordContext ctx);
	/**
	 * Enter a parse tree produced by the {@code typeEnum}
	 * labeled alternative in {@link MiniCParser#type}.
	 * @param ctx the parse tree
	 */
	void enterTypeEnum(MiniCParser.TypeEnumContext ctx);
	/**
	 * Exit a parse tree produced by the {@code typeEnum}
	 * labeled alternative in {@link MiniCParser#type}.
	 * @param ctx the parse tree
	 */
	void exitTypeEnum(MiniCParser.TypeEnumContext ctx);
	/**
	 * Enter a parse tree produced by the {@code affectableArray}
	 * labeled alternative in {@link MiniCParser#affectable}.
	 * @param ctx the parse tree
	 */
	void enterAffectableArray(MiniCParser.AffectableArrayContext ctx);
	/**
	 * Exit a parse tree produced by the {@code affectableArray}
	 * labeled alternative in {@link MiniCParser#affectable}.
	 * @param ctx the parse tree
	 */
	void exitAffectableArray(MiniCParser.AffectableArrayContext ctx);
	/**
	 * Enter a parse tree produced by the {@code affectableIdentifiant}
	 * labeled alternative in {@link MiniCParser#affectable}.
	 * @param ctx the parse tree
	 */
	void enterAffectableIdentifiant(MiniCParser.AffectableIdentifiantContext ctx);
	/**
	 * Exit a parse tree produced by the {@code affectableIdentifiant}
	 * labeled alternative in {@link MiniCParser#affectable}.
	 * @param ctx the parse tree
	 */
	void exitAffectableIdentifiant(MiniCParser.AffectableIdentifiantContext ctx);
	/**
	 * Enter a parse tree produced by the {@code affectableField}
	 * labeled alternative in {@link MiniCParser#affectable}.
	 * @param ctx the parse tree
	 */
	void enterAffectableField(MiniCParser.AffectableFieldContext ctx);
	/**
	 * Exit a parse tree produced by the {@code affectableField}
	 * labeled alternative in {@link MiniCParser#affectable}.
	 * @param ctx the parse tree
	 */
	void exitAffectableField(MiniCParser.AffectableFieldContext ctx);
	/**
	 * Enter a parse tree produced by the {@code affectablePointer}
	 * labeled alternative in {@link MiniCParser#affectable}.
	 * @param ctx the parse tree
	 */
	void enterAffectablePointer(MiniCParser.AffectablePointerContext ctx);
	/**
	 * Exit a parse tree produced by the {@code affectablePointer}
	 * labeled alternative in {@link MiniCParser#affectable}.
	 * @param ctx the parse tree
	 */
	void exitAffectablePointer(MiniCParser.AffectablePointerContext ctx);
	/**
	 * Enter a parse tree produced by the {@code affectableConversion}
	 * labeled alternative in {@link MiniCParser#affectable}.
	 * @param ctx the parse tree
	 */
	void enterAffectableConversion(MiniCParser.AffectableConversionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code affectableConversion}
	 * labeled alternative in {@link MiniCParser#affectable}.
	 * @param ctx the parse tree
	 */
	void exitAffectableConversion(MiniCParser.AffectableConversionContext ctx);
	/**
	 * Enter a parse tree produced by {@link MiniCParser#expressions}.
	 * @param ctx the parse tree
	 */
	void enterExpressions(MiniCParser.ExpressionsContext ctx);
	/**
	 * Exit a parse tree produced by {@link MiniCParser#expressions}.
	 * @param ctx the parse tree
	 */
	void exitExpressions(MiniCParser.ExpressionsContext ctx);
	/**
	 * Enter a parse tree produced by {@link MiniCParser#arguments}.
	 * @param ctx the parse tree
	 */
	void enterArguments(MiniCParser.ArgumentsContext ctx);
	/**
	 * Exit a parse tree produced by {@link MiniCParser#arguments}.
	 * @param ctx the parse tree
	 */
	void exitArguments(MiniCParser.ArgumentsContext ctx);
	/**
	 * Enter a parse tree produced by the {@code expressionCharacter}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterExpressionCharacter(MiniCParser.ExpressionCharacterContext ctx);
	/**
	 * Exit a parse tree produced by the {@code expressionCharacter}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitExpressionCharacter(MiniCParser.ExpressionCharacterContext ctx);
	/**
	 * Enter a parse tree produced by the {@code expressionAddress}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterExpressionAddress(MiniCParser.ExpressionAddressContext ctx);
	/**
	 * Exit a parse tree produced by the {@code expressionAddress}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitExpressionAddress(MiniCParser.ExpressionAddressContext ctx);
	/**
	 * Enter a parse tree produced by the {@code expressionOpposite}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterExpressionOpposite(MiniCParser.ExpressionOppositeContext ctx);
	/**
	 * Exit a parse tree produced by the {@code expressionOpposite}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitExpressionOpposite(MiniCParser.ExpressionOppositeContext ctx);
	/**
	 * Enter a parse tree produced by the {@code expressionParenthese}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterExpressionParenthese(MiniCParser.ExpressionParentheseContext ctx);
	/**
	 * Exit a parse tree produced by the {@code expressionParenthese}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitExpressionParenthese(MiniCParser.ExpressionParentheseContext ctx);
	/**
	 * Enter a parse tree produced by the {@code expressionSequence}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterExpressionSequence(MiniCParser.ExpressionSequenceContext ctx);
	/**
	 * Exit a parse tree produced by the {@code expressionSequence}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitExpressionSequence(MiniCParser.ExpressionSequenceContext ctx);
	/**
	 * Enter a parse tree produced by the {@code expressionNot}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterExpressionNot(MiniCParser.ExpressionNotContext ctx);
	/**
	 * Exit a parse tree produced by the {@code expressionNot}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitExpressionNot(MiniCParser.ExpressionNotContext ctx);
	/**
	 * Enter a parse tree produced by the {@code expressionConditional}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterExpressionConditional(MiniCParser.ExpressionConditionalContext ctx);
	/**
	 * Exit a parse tree produced by the {@code expressionConditional}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitExpressionConditional(MiniCParser.ExpressionConditionalContext ctx);
	/**
	 * Enter a parse tree produced by the {@code expressionAnd}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterExpressionAnd(MiniCParser.ExpressionAndContext ctx);
	/**
	 * Exit a parse tree produced by the {@code expressionAnd}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitExpressionAnd(MiniCParser.ExpressionAndContext ctx);
	/**
	 * Enter a parse tree produced by the {@code expressionArrayAcess}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterExpressionArrayAcess(MiniCParser.ExpressionArrayAcessContext ctx);
	/**
	 * Exit a parse tree produced by the {@code expressionArrayAcess}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitExpressionArrayAcess(MiniCParser.ExpressionArrayAcessContext ctx);
	/**
	 * Enter a parse tree produced by the {@code expressionCouple}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterExpressionCouple(MiniCParser.ExpressionCoupleContext ctx);
	/**
	 * Exit a parse tree produced by the {@code expressionCouple}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitExpressionCouple(MiniCParser.ExpressionCoupleContext ctx);
	/**
	 * Enter a parse tree produced by the {@code expressionAccess}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterExpressionAccess(MiniCParser.ExpressionAccessContext ctx);
	/**
	 * Exit a parse tree produced by the {@code expressionAccess}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitExpressionAccess(MiniCParser.ExpressionAccessContext ctx);
	/**
	 * Enter a parse tree produced by the {@code expressionField}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterExpressionField(MiniCParser.ExpressionFieldContext ctx);
	/**
	 * Exit a parse tree produced by the {@code expressionField}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitExpressionField(MiniCParser.ExpressionFieldContext ctx);
	/**
	 * Enter a parse tree produced by the {@code expressionNull}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterExpressionNull(MiniCParser.ExpressionNullContext ctx);
	/**
	 * Exit a parse tree produced by the {@code expressionNull}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitExpressionNull(MiniCParser.ExpressionNullContext ctx);
	/**
	 * Enter a parse tree produced by the {@code expressionPointerAccess}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterExpressionPointerAccess(MiniCParser.ExpressionPointerAccessContext ctx);
	/**
	 * Exit a parse tree produced by the {@code expressionPointerAccess}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitExpressionPointerAccess(MiniCParser.ExpressionPointerAccessContext ctx);
	/**
	 * Enter a parse tree produced by the {@code expressionConversion}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterExpressionConversion(MiniCParser.ExpressionConversionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code expressionConversion}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitExpressionConversion(MiniCParser.ExpressionConversionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code expressionEquality}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterExpressionEquality(MiniCParser.ExpressionEqualityContext ctx);
	/**
	 * Exit a parse tree produced by the {@code expressionEquality}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitExpressionEquality(MiniCParser.ExpressionEqualityContext ctx);
	/**
	 * Enter a parse tree produced by the {@code expressionInequality}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterExpressionInequality(MiniCParser.ExpressionInequalityContext ctx);
	/**
	 * Exit a parse tree produced by the {@code expressionInequality}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitExpressionInequality(MiniCParser.ExpressionInequalityContext ctx);
	/**
	 * Enter a parse tree produced by the {@code expressionFirst}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterExpressionFirst(MiniCParser.ExpressionFirstContext ctx);
	/**
	 * Exit a parse tree produced by the {@code expressionFirst}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitExpressionFirst(MiniCParser.ExpressionFirstContext ctx);
	/**
	 * Enter a parse tree produced by the {@code expressionFunctionCall}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterExpressionFunctionCall(MiniCParser.ExpressionFunctionCallContext ctx);
	/**
	 * Exit a parse tree produced by the {@code expressionFunctionCall}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitExpressionFunctionCall(MiniCParser.ExpressionFunctionCallContext ctx);
	/**
	 * Enter a parse tree produced by the {@code expressionAdditive}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterExpressionAdditive(MiniCParser.ExpressionAdditiveContext ctx);
	/**
	 * Exit a parse tree produced by the {@code expressionAdditive}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitExpressionAdditive(MiniCParser.ExpressionAdditiveContext ctx);
	/**
	 * Enter a parse tree produced by the {@code expressionTrue}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterExpressionTrue(MiniCParser.ExpressionTrueContext ctx);
	/**
	 * Exit a parse tree produced by the {@code expressionTrue}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitExpressionTrue(MiniCParser.ExpressionTrueContext ctx);
	/**
	 * Enter a parse tree produced by the {@code expressionMultiplicative}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterExpressionMultiplicative(MiniCParser.ExpressionMultiplicativeContext ctx);
	/**
	 * Exit a parse tree produced by the {@code expressionMultiplicative}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitExpressionMultiplicative(MiniCParser.ExpressionMultiplicativeContext ctx);
	/**
	 * Enter a parse tree produced by the {@code expressionFalse}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterExpressionFalse(MiniCParser.ExpressionFalseContext ctx);
	/**
	 * Exit a parse tree produced by the {@code expressionFalse}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitExpressionFalse(MiniCParser.ExpressionFalseContext ctx);
	/**
	 * Enter a parse tree produced by the {@code expresionFloat}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterExpresionFloat(MiniCParser.ExpresionFloatContext ctx);
	/**
	 * Exit a parse tree produced by the {@code expresionFloat}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitExpresionFloat(MiniCParser.ExpresionFloatContext ctx);
	/**
	 * Enter a parse tree produced by the {@code expressionSecond}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterExpressionSecond(MiniCParser.ExpressionSecondContext ctx);
	/**
	 * Exit a parse tree produced by the {@code expressionSecond}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitExpressionSecond(MiniCParser.ExpressionSecondContext ctx);
	/**
	 * Enter a parse tree produced by the {@code expressionArrayAllocation}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterExpressionArrayAllocation(MiniCParser.ExpressionArrayAllocationContext ctx);
	/**
	 * Exit a parse tree produced by the {@code expressionArrayAllocation}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitExpressionArrayAllocation(MiniCParser.ExpressionArrayAllocationContext ctx);
	/**
	 * Enter a parse tree produced by the {@code expressionString}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterExpressionString(MiniCParser.ExpressionStringContext ctx);
	/**
	 * Exit a parse tree produced by the {@code expressionString}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitExpressionString(MiniCParser.ExpressionStringContext ctx);
	/**
	 * Enter a parse tree produced by the {@code expressionOr}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterExpressionOr(MiniCParser.ExpressionOrContext ctx);
	/**
	 * Exit a parse tree produced by the {@code expressionOr}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitExpressionOr(MiniCParser.ExpressionOrContext ctx);
	/**
	 * Enter a parse tree produced by the {@code expressionPointerAllocation}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterExpressionPointerAllocation(MiniCParser.ExpressionPointerAllocationContext ctx);
	/**
	 * Exit a parse tree produced by the {@code expressionPointerAllocation}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitExpressionPointerAllocation(MiniCParser.ExpressionPointerAllocationContext ctx);
	/**
	 * Enter a parse tree produced by the {@code expressionInt}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterExpressionInt(MiniCParser.ExpressionIntContext ctx);
	/**
	 * Exit a parse tree produced by the {@code expressionInt}
	 * labeled alternative in {@link MiniCParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitExpressionInt(MiniCParser.ExpressionIntContext ctx);
	/**
	 * Enter a parse tree produced by {@link MiniCParser#identifiant}.
	 * @param ctx the parse tree
	 */
	void enterIdentifiant(MiniCParser.IdentifiantContext ctx);
	/**
	 * Exit a parse tree produced by {@link MiniCParser#identifiant}.
	 * @param ctx the parse tree
	 */
	void exitIdentifiant(MiniCParser.IdentifiantContext ctx);
}