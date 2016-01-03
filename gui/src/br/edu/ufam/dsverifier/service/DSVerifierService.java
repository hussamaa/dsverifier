package br.edu.ufam.dsverifier.service;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.concurrent.TimeUnit;

import br.edu.ufam.dsverifier.domain.Verification;
import br.edu.ufam.dsverifier.domain.enums.VerificationStatus;
import br.edu.ufam.dsverifier.util.DSVerifierUtils;

public class DSVerifierService {

	public static final String DSVERIFIER_EXECUTABLE = "dsverifier";
	public static final String DSVERIFIER_PARAMETERS = "-DBMC=ESBMC -I $DSVERIFIER_HOME/bmc";
	
	private static DSVerifierService instance;
	
	private DSVerifierService(){		
	}
	
	public static DSVerifierService getInstance(){		
		if (instance == null){
			instance = new DSVerifierService();
		}
		return instance;				
	}
	
	public void callDSVerifier(Verification verification) throws Exception {	
		File verificationFile = verification.getFile();
		String verificationFilePath = verificationFile.getAbsolutePath();
		StringBuilder commandLine = new StringBuilder(DSVERIFIER_EXECUTABLE + " " + verificationFilePath);
		
		/* include the property */
		commandLine.append(" --property " + verification.getProperty());
		/* include the realization */
		commandLine.append(" --realization " + verification.getImplementation().getRealization());	
		/* include x size */
		commandLine.append(" --x-size " + verification.getBound());	
		
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
	
	public void generateVerificationFile(Verification verification) throws IOException{
		
		StringBuilder content = new StringBuilder();			
		content.append("#include <dsverifier.h>\n\n");
		content.append("digital_system ds = {\n");
		content.append("\t.a = " + verification.getDigitalSystem().getDenominator() + ",\n");
		content.append("\t.a_size = " + verification.getDigitalSystem().getDenominatorSize() + ",\n");
		content.append("\t.b = " + verification.getDigitalSystem().getNumerator() + ",\n");
		content.append("\t.b_size = " + verification.getDigitalSystem().getNumeratorSize() + "\n");
		content.append("};\n");
		
		content.append("\nimplementation impl = {\n");
		content.append("\t.int_bits = " + verification.getImplementation().getIntegerBits() + ",\n");
		content.append("\t.frac_bits = " + verification.getImplementation().getPrecisionBits() + ",\n");
		content.append("\t.min = " + verification.getImplementation().getMinimum() + ",\n");
		content.append("\t.max = " + verification.getImplementation().getMaximum() + ",\n");
		content.append("\t.scale = " + verification.getImplementation().getScale() + "");

		if (verification.getImplementation().getDelta() != null){
			content.append(",\n\t.delta = " + verification.getImplementation().getDelta() + "");
		}
		
		content.append("\n};\n");
		
		/* create file content */
		verification.setFileContent(content.toString());		
			
		File verificationTmpFile = File.createTempFile("dsverifier", ".c", new File("."));
		verification.setFile(verificationTmpFile);
		
		/* write in temporary file */
		FileWriter fileWriter = new FileWriter(verificationTmpFile.getAbsoluteFile());
		BufferedWriter bufferedWriter = new BufferedWriter(fileWriter);
		bufferedWriter.write(content.toString());
		bufferedWriter.close();		
		
	}
	
	public void generateClosedLoopVerificationFile(Verification verification) throws IOException{
		
		StringBuilder content = new StringBuilder();			
		content.append("#include <dsverifier.h>\n\n");
		content.append("digital_system control = {\n");
		content.append("\t.a = " + verification.getControl().getDenominator() + ",\n");
		content.append("\t.a_size = " + verification.getControl().getDenominatorSize() + ",\n");
		content.append("\t.b = " + verification.getControl().getNumerator() + ",\n");
		content.append("\t.b_size = " + verification.getControl().getNumeratorSize() + "\n");
		content.append("};\n");
		
		content.append("\ndigital_system plant = {\n");
		content.append("\t.a = " + verification.getPlant().getDenominator() + ",\n");
		content.append("\t.a_size = " + verification.getPlant().getDenominatorSize() + ",\n");
		content.append("\t.b = " + verification.getPlant().getNumerator() + ",\n");
		content.append("\t.b_size = " + verification.getPlant().getNumeratorSize() + "\n");
		content.append("};\n");
		
		content.append("\nimplementation impl = {\n");
		content.append("\t.int_bits = " + verification.getImplementation().getIntegerBits() + ",\n");
		content.append("\t.frac_bits = " + verification.getImplementation().getPrecisionBits() + ",\n");
		content.append("\t.scale = " + verification.getImplementation().getScale() + "");

		if (verification.getImplementation().getDelta() != null){
			content.append(",\n\t.delta = " + verification.getImplementation().getDelta() + "");
		}
		
		content.append("\n};\n");
		
		/* create file content */
		verification.setFileContent(content.toString());		
			
		File verificationTmpFile = File.createTempFile("dsverifier-cloop", ".c", new File("."));
		verification.setFile(verificationTmpFile);
		
		/* write in temporary file */
		FileWriter fileWriter = new FileWriter(verificationTmpFile.getAbsoluteFile());
		BufferedWriter bufferedWriter = new BufferedWriter(fileWriter);
		bufferedWriter.write(content.toString());
		bufferedWriter.close();		
		
	}
	
}