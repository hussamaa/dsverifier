package br.edu.ufam.dsverifier.domain;

import java.io.File;
import java.util.Calendar;

import br.edu.ufam.dsverifier.domain.enums.DigitalSystemProperties;
import br.edu.ufam.dsverifier.domain.enums.DigitalSystemRealizations;
import br.edu.ufam.dsverifier.domain.enums.VerificationStatus;

public class Verification {

	private DigitalSystem digitalSystem;
	private Implementation implementation;
	private DigitalSystemRealizations realization;
	private DigitalSystemProperties property;

	private Calendar date;
	private String fileContent;
	private File file;

	private VerificationStatus status;
	private String output;

	public Implementation getImplementation() {
		return implementation;
	}

	public void setImplementation(Implementation impl) {
		this.implementation = impl;
	}

	public Calendar getDate() {
		return date;
	}

	public void setDate(Calendar date) {
		this.date = date;
	}

	public String getFileContent() {
		return fileContent;
	}

	public void setFileContent(String fileContent) {
		this.fileContent = fileContent;
	}

	public File getFile() {
		return file;
	}

	public void setFile(File file) {
		this.file = file;
	}

	public VerificationStatus getStatus() {
		return status;
	}

	public void setStatus(VerificationStatus status) {
		this.status = status;
	}

	public DigitalSystem getDigitalSystem() {
		return digitalSystem;
	}

	public void setDigitalSystem(DigitalSystem digitalSystem) {
		this.digitalSystem = digitalSystem;
	}

	public DigitalSystemProperties getProperty() {
		return property;
	}

	public void setProperty(DigitalSystemProperties property) {
		this.property = property;
	}

	public DigitalSystemRealizations getRealization() {
		return realization;
	}

	public void setRealization(DigitalSystemRealizations realization) {
		this.realization = realization;
	}

	public String getOutput() {
		return output;
	}

	public void setOutput(String output) {
		this.output = output;
	}

}