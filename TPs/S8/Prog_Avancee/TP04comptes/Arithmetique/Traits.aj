public aspect Traits {
    int nombreTraits = 0;

    public int Constante.nombreTraits() {
		return 0;
	}
	
	public int AccesVariable.nombreTraits() {
		return 0;
	}

	public int Addition.nombreTraits() {
		return 2;
	}

	public int Negation.nombreTraits() {
		return 1;
	}

	public int Multiplication.nombreTraits() {
		return 3;
	}

    public int ExpressionBinaire.nbTraits() {
		return this.getOperandeGauche().nbTraits()
				+ this.getOperandeDroite().nbTraits()
				+ this.getOperateur().nbTraits();
	}

	public int ExpressionUnaire.nbTraits() {
		return this.getOperande().nbTraits()
				+ this.getOperateur().nbTraits();
	}
	
	public abstract int OperateurUnaire.nbTraits();
	public abstract int OperateurBinaire.nbTraits();


    
}