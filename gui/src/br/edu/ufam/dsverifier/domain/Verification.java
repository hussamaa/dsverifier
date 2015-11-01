package br.edu.ufam.dsverifier.domain;

import java.io.File;
import java.util.Calendar;

import br.edu.ufam.dsverifier.domain.enums.DigitalSystemProperties;
import br.edu.ufam.dsverifier.domain.enums.VerificationStatus;

public class Verification {

	private DigitalSystem digitalSystem;
	private DigitalSystem control;
	private DigitalSystem plant;
	private Implementation implementation;
	private DigitalSystemProperties property;
	private Integer bound;

	private Calendar date;
	private Long time;
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

	public String getOutput() {
		return output;
	}

	public void setOutput(String output) {
		this.output = output;
	}

	public Long getTime() {
		return time;
	}

	public void setTime(Long time) {
		this.time = time;
	}

	public Integer getBound() {
		return bound;
	}

	public void setBound(Integer bound) {
		this.bound = bound;
	}

	public DigitalSystem getControl() {
		return control;
	}

	public void setControl(DigitalSystem control) {
		this.control = control;
	}

	public DigitalSystem getPlant() {
		return plant;
	}

	public void setPlant(DigitalSystem plant) {
		this.plant = plant;
	}

}