package br.edu.ufam.dsverifier.application;

import java.io.IOException;
import java.net.URL;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.ResourceBundle;
import java.util.Set;

import javafx.fxml.FXML;
import javafx.fxml.Initializable;
import javafx.scene.control.CheckBox;
import javafx.scene.control.TabPane;
import javafx.scene.control.TextArea;
import javafx.scene.control.TextField;

import javax.swing.JOptionPane;

import br.edu.ufam.dsverifier.domain.DigitalSystem;
import br.edu.ufam.dsverifier.domain.Implementation;
import br.edu.ufam.dsverifier.domain.Verification;
import br.edu.ufam.dsverifier.domain.enums.DigitalSystemProperties;
import br.edu.ufam.dsverifier.domain.enums.DigitalSystemRealizations;
import br.edu.ufam.dsverifier.service.DSVerifierService;

public class PrincipalController implements Initializable{

	@FXML
	private TabPane tabPane;
	
	@FXML
	private TextField tfNumerator;
	
	@FXML
	private TextField tfDenominator;
	
	@FXML
	private TextField tfIntegerBits;
	
	@FXML
	private TextField tfPrecisionBits;
	
	@FXML
	private CheckBox checkOverflow;
	
	@FXML
	private CheckBox checkLimitCycle;
	
	@FXML
	private CheckBox checkTiming;
	
	@FXML
	private CheckBox checkError;
	
	@FXML
	private CheckBox checkStability;
	
	@FXML
	private CheckBox checkMinimumPhase;
	
	@FXML
	private TextArea consoleOutput;

	@Override
	public void initialize(URL location, ResourceBundle resources) {
	}
	
	/**
	 * validate parameters and generate the list of verifications
	 * @throws IOException 
	 */
	public List<Verification> validate() throws IOException{
		System.out.println("validate");
		
		/* digital system */
		DigitalSystem ds = validateDigitalSystem();
		if (ds == null) return null;
	
		/* implementation */
		Implementation impl = validateImplementation();
		if (impl == null) return null;
		
		/* prepare a list of properties to check */
		Set<DigitalSystemProperties> properties = validateProperties();
		if (properties == null) return null;
		
		/* create the verification list */
		List<Verification> verifications = new ArrayList<Verification>();		
		for (DigitalSystemProperties property : properties) {
			Verification verification = new Verification();
			verification.setDigitalSystem(ds);
			verification.setImplementation(impl);
			verification.setProperty(property);
			verification.setRealization(DigitalSystemRealizations.DFI);
			DSVerifierService.getInstance().generateVerificationFile(verification);
			verifications.add(verification);
		}
		
		System.out.println("Verification List: " + verifications.size());
		
		return verifications;
	}
	
	/* generate digital system */
	public DigitalSystem validateDigitalSystem(){
		
		String numerator = tfNumerator.getText();
		String denominator = tfDenominator.getText();

		if (numerator.length() == 0){
			JOptionPane.showMessageDialog(null, "You need to input the digital system numerator");
			return null;
		}		
		int numeratorSize = numerator.split(",").length;
			
		if (denominator.length() == 0){
			JOptionPane.showMessageDialog(null, "You need to input the digital system denominator");
			return null;
		}
		int denominatorSize = denominator.split(",").length;

		DigitalSystem ds =  new DigitalSystem();
		ds.setNumerator(numerator);
		ds.setNumeratorSize(numeratorSize);
		ds.setDenominator(denominator);
		ds.setDenominatorSize(denominatorSize);

		return ds;
	}
	
	/* generate implementation */
	public Implementation validateImplementation(){
				
		String integerBits = tfIntegerBits.getText();
		String precisionBits = tfPrecisionBits.getText();

		if (integerBits.length() == 0){
			JOptionPane.showMessageDialog(null, "You need to input the number of integer bits in implementation");
			return null;
		}
			
		if (precisionBits.length() == 0){
			JOptionPane.showMessageDialog(null, "You need to input the number of precision bits in implementation");
			return null;
		}

		Implementation impl = new Implementation();
		impl.setIntegerBits(Integer.valueOf(integerBits));
		impl.setPrecisionBits(Integer.valueOf(precisionBits));		
	
		return impl;
	}
	
	/* generate properties to check */
	public Set<DigitalSystemProperties> validateProperties(){

		Set<DigitalSystemProperties> properties = new HashSet<DigitalSystemProperties>();
		if (checkOverflow.isSelected())
			properties.add(DigitalSystemProperties.OVERFLOW);
		if (checkLimitCycle.isSelected())
			properties.add(DigitalSystemProperties.LIMIT_CYCLE);
		if (checkTiming.isSelected())
			properties.add(DigitalSystemProperties.TIMING);
		if (checkError.isSelected())
			properties.add(DigitalSystemProperties.ERROR);
		if (checkMinimumPhase.isSelected())
			properties.add(DigitalSystemProperties.MINIMUM_PHASE);
		if (checkStability.isSelected())
			properties.add(DigitalSystemProperties.STABILITY);
		
		if (properties.size() == 0){
			JOptionPane.showMessageDialog(null, "You need to select a property to check");
			return null;
		}
		
		return properties;
	}
	
	/* call esbmc + dsverifier to check properties */
	public void verifyDigitalSystem() throws Exception{
		consoleOutput.clear();
		List<Verification> verifications = validate();		
		System.out.println("Clicou em verificar digital system");
		if (verifications == null) return; 
		for (Verification verification : verifications) {
			DSVerifierService.getInstance().callDSVerifier(verification);
			consoleOutput.setText(verification.getOutput());
		}
	}
	
	public void nextStep(){
		System.out.println("proxima aba");
	}

}
