package br.edu.ufam.dsverifier.domain;

public class DigitalSystem {

	private String numerator;
	private String denominator;
	private Double sampleTime;

	private int numeratorSize;
	private int denominatorSize;

	public String getNumerator() {
		return numerator;
	}

	public void setNumerator(String numerator) {
		this.numerator = numerator;
	}

	public String getDenominator() {
		return denominator;
	}

	public void setDenominator(String denominator) {
		this.denominator = denominator;
	}

	public Double getSampleTime() {
		return sampleTime;
	}

	public void setSampleTime(Double sampleTime) {
		this.sampleTime = sampleTime;
	}

	public int getNumeratorSize() {
		return numeratorSize;
	}

	public void setNumeratorSize(int numeratorSize) {
		this.numeratorSize = numeratorSize;
	}

	public int getDenominatorSize() {
		return denominatorSize;
	}

	public void setDenominatorSize(int denominatorSize) {
		this.denominatorSize = denominatorSize;
	}

}