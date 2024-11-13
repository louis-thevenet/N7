import java.util.Set;

import javax.annotation.processing.AbstractProcessor;
import javax.annotation.processing.Messager;
import javax.annotation.processing.RoundEnvironment;
import javax.annotation.processing.SupportedAnnotationTypes;
import javax.annotation.processing.SupportedSourceVersion;
import javax.lang.model.SourceVersion;
import javax.lang.model.element.Element;
import javax.lang.model.element.ElementKind;
import javax.lang.model.element.Modifier;
import javax.lang.model.element.TypeElement;
import javax.tools.Diagnostic.Kind;

/** Check that a class marked {@code @Utility} is indeed a utility class. */
@SupportedAnnotationTypes("Utility")
@SupportedSourceVersion(SourceVersion.RELEASE_21)
public class UtilityProcessor extends AbstractProcessor {

	@Override
	public boolean process(
			Set<? extends TypeElement> annotations,
			RoundEnvironment roundingEnvironment) {
		Messager messager = processingEnv.getMessager();
		messager.printMessage(Kind.NOTE,
				"UtilityProcessor executed.");
		messager.printMessage(Kind.WARNING,
				"The provided UtilityProcessor class is wrong.  Correct it!");
		for (TypeElement te : annotations) {
			for (Element elt : roundingEnvironment.getElementsAnnotatedWith(te)) {
				if (elt.getKind() == ElementKind.CLASS) { // elt is a class
					// Check that the class is declared final
					if (!elt.getModifiers().contains(Modifier.FINAL)) {

						messager.printMessage(Kind.ERROR,
								"Class is not final:", elt);
					}

					// Check that enclosed elements are static
					for (var inner : elt.getEnclosedElements()) {
						if (inner.getKind().isDeclaredType() && !inner.getModifiers().contains(Modifier.STATIC)) {

							messager.printMessage(Kind.ERROR,
									"Inner element " + inner.getSimpleName() + " is not static");
						}
					}

				} else {
					messager.printMessage(Kind.ERROR,
							"@Utility applies to class only:", elt);
				}
			}
		}
		return true;
	}

}
