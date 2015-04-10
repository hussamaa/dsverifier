package br.edu.ufam.dsverifier.util;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.StringReader;

import javafx.geometry.Insets;
import javafx.scene.control.TextField;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Region;

import org.controlsfx.control.RangeSlider;

import br.edu.ufam.dsverifier.domain.Verification;

public class DSVerifierUtils {

	private static DSVerifierUtils instance;

	private DSVerifierUtils() {
	}

	public static DSVerifierUtils getInstance() {
		if (instance == null) {
			instance = new DSVerifierUtils();
		}
		return instance;
	}

	public String callCommandLine(String commandLine) throws IOException,
			InterruptedException {
		Process p = Runtime.getRuntime().exec(commandLine);
		InputStream inputStream = p.getInputStream();
		InputStreamReader inputStreamReader = new InputStreamReader(inputStream);
		BufferedReader bufferedReader = new BufferedReader(inputStreamReader);
		StringBuilder output = new StringBuilder();
		String line;
		while ((line = bufferedReader.readLine()) != null) {
		//	System.out.println(line); // it prints all at once after command has
										// been executed.
			output.append(line + "\n");
		}
		p.waitFor();
		return output.toString();
	}
	
	public Region createHorizontalSlider(TextField minField, TextField maxField) {
        
		minField.setPrefColumnCount(2);
        maxField.setPrefColumnCount(2);
 
        final RangeSlider hSlider = new RangeSlider(-10, 10, -1, 1);
        hSlider.setShowTickMarks(true);
        hSlider.setShowTickLabels(true);
        hSlider.setBlockIncrement(10);
        hSlider.setPrefWidth(100);
 
        minField.setText("" + hSlider.getLowValue());
        maxField.setText("" + hSlider.getHighValue());
 
        minField.setEditable(false);
        minField.setPromptText("Min");
 
        maxField.setEditable(false);
        maxField.setPromptText("Max");
 
        minField.textProperty().bind(hSlider.lowValueProperty().asString("%.0f"));
        maxField.textProperty().bind(hSlider.highValueProperty().asString("%.0f"));
 
        HBox box = new HBox(10);
        box.getChildren().addAll(minField, hSlider, maxField);
        box.setPadding(new Insets(20,0,0,20));
        box.setFillHeight(false);
 
        return box;
    }
	
	public void removeTemporaryFiles(){
		String temporaryFolderPath = System.getProperty("java.io.tmpdir");
		
		File temporaryFolder = new File(temporaryFolderPath);		
		File[] listFiles = temporaryFolder.listFiles();
		
		/* remove temporary files */
		for (File file : listFiles) {
			if (file.isFile()){
				if ((file.getName().indexOf("dsverifier") != -1) && (file.getName().endsWith(".c"))){
					file.delete();
				}
			}
		}		
	}
	
	public Double isNumeric(String str)  {  
		Double value;
		try{  
			value = Double.parseDouble(str);  
		}  
		catch(NumberFormatException nfe){  
			return null;  
		}  
		return value;  
	}
	
	public double[] getArrayInputsFromVerification(Verification verification) throws FileNotFoundException, IOException{

		int precisionBits = verification.getImplementation().getPrecisionBits();
		String filename = verification.getFile().getName().substring(0, verification.getFile().getName().length() - 2);
		
		String inputString= ""; 
		try(BufferedReader br = new BufferedReader(new StringReader(verification.getOutput()))) {
	        String line = br.readLine();	     
	        while (line != null) {
	            line = br.readLine();
	            if ((line != null) && (line.indexOf(filename + "::verify_overflow::1::x={") != -1)){
	            	inputString = line;	            	
	            }
	        }
	    } 
		inputString = inputString.replaceAll(", nil", ""); 
		inputString = inputString.replace(filename + "::verify_overflow::1::x={", "");
		inputString = inputString.replace("}", "");
		
		String[] inputsStr = inputString.split(",");
		double inputs[] = new double [inputsStr.length];

		for (int i=0; i < inputsStr.length; i++) {
			inputs[i] = Double.valueOf(inputsStr[i]) / Math.pow(2,precisionBits);
			System.out.println(inputs[i]);
		}
		
		return inputs;
	}	
	
}