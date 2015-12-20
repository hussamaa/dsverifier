package br.edu.ufam.dsverifier.service;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.util.concurrent.TimeUnit;

import br.edu.ufam.dsverifier.domain.SpaceState;
import br.edu.ufam.dsverifier.domain.Verification;
import br.edu.ufam.dsverifier.domain.enums.DigitalSystemProperties;
import br.edu.ufam.dsverifier.domain.enums.VerificationStatus;
import br.edu.ufam.dsverifier.util.DSVerifierUtils;
import br.edu.ufam.dsverifier.util.SpaceStateUtils;

public class DSVerifierSpaceStateService {

	public static final String DSVERIFIER_EXECUTABLE = "./dsverifier";
	public static final String DSVERIFIER_PARAMETERS = "-DBMC=ESBMC -DJACKSON_RULE";
	
	private static DSVerifierSpaceStateService instance;
	
	private DSVerifierSpaceStateService(){		
	}
	
	public static DSVerifierSpaceStateService getInstance(){		
		if (instance == null){
			instance = new DSVerifierSpaceStateService();
		}
		return instance;				
	}
	
	public void callDSVerifier(Verification verification) throws Exception {	
		File verificationFile = verification.getFile();
		String verificationFilePath = verificationFile.getAbsolutePath();
		
		StringBuilder commandLine = new StringBuilder(DSVERIFIER_EXECUTABLE + " " + verificationFilePath);
		
		/* include the property */
		commandLine.append(" --property " + verification.getProperty());
		
		/* include x size */
		if (verification.getProperty().equals(DigitalSystemProperties.QUANTISATION_ERROR)) {
			commandLine.append(" --limit " + verification.getSpaceState().getErrorLimit());
			commandLine.append(" --x-size " + verification.getBound());
		}
		
		commandLine.append(" --bmc CBMC");
		
		if (verification.getSpaceState().isClosedLoop()){
			commandLine.append(" --closed-loop");
		}
		
		System.out.println("COMMAND LINE: " + commandLine.toString());
		
		long initialTime = System.nanoTime();  
		String output = DSVerifierUtils.getInstance().callCommandLine(commandLine.toString());
		long finalTime = System.nanoTime();  
		long seconds = TimeUnit.SECONDS.convert(finalTime - initialTime, TimeUnit.NANOSECONDS);
		
		verification.setTime(seconds);
		verification.setOutput(output);
		if (output.indexOf("VERIFICATION FAILED") != -1){
			verification.setStatus(VerificationStatus.VERIFICATION_FAILED);
		}else if (output.indexOf("VERIFICATION SUCCESSFUL") != -1){
			verification.setStatus(VerificationStatus.VERIFICATION_SUCCESSFUL);
		}else{
			verification.setStatus(VerificationStatus.UNKNOWN);
		}
	}
	
	public String prepareCommandLine(Verification verification){
		String commandLine = DSVERIFIER_EXECUTABLE + " " + DSVERIFIER_PARAMETERS + " ";
		return commandLine;		
	}	

	public void generateSpaceStateVerificationFile(Verification verification) {
		
		StringBuilder content = new StringBuilder();			
		try {
			final FileReader inputFile = new FileReader("file.ss");
			final BufferedReader bufferReader = new BufferedReader(inputFile);
			String line;
			while ((line = bufferReader.readLine()) != null) {
				content.append(line + "\n");
			}
			bufferReader.close();
		} catch (final Exception e) {
			System.out.println("Error while reading file line by line:"
					+ e.getMessage());
		}
		
		/* create file content */
		verification.setFileContent(content.toString());		
			
		verification.setFile(new File("file.ss"));
	}
	
	public SpaceState getSpaceState() {
		
		StringBuilder content = new StringBuilder();
		final SpaceState spaceState = new SpaceState();
		try {
			final FileReader inputFile = new FileReader("file.ss");
			final BufferedReader bufferReader = new BufferedReader(inputFile);
			String line;
			while ((line = bufferReader.readLine()) != null) {
				content.append(line + "\n");
			}
			bufferReader.close();
		} catch (final Exception e) {
			System.out.println("Error while reading file line by line:"
					+ e.getMessage());
		}
		
		SpaceStateUtils.setSpaceStateObject(content, spaceState);
		
		return spaceState;
	}	
}