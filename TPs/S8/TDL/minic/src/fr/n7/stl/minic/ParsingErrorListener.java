package fr.n7.stl.minic;

import org.antlr.v4.runtime.BaseErrorListener;
import org.antlr.v4.runtime.RecognitionException;
import org.antlr.v4.runtime.Recognizer;

public class ParsingErrorListener extends BaseErrorListener {

    private boolean hasError;

    public ParsingErrorListener() {
        super();
        this.hasError = false;
    }

    @Override
    public void syntaxError(Recognizer<?, ?> recognizer, Object offendingSymbol, int line, int charPositionInLine,
            String msg, RecognitionException e) {
        this.hasError = true;
    }

    public boolean hasError() {
        return this.hasError;
    }
}
