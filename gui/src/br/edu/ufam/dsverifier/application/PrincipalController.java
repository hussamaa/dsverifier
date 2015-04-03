package br.edu.ufam.dsverifier.application;

import java.io.IOException;
import java.net.URL;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.ResourceBundle;
import java.util.Set;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.atomic.AtomicInteger;

import javafx.concurrent.Task;
import javafx.fxml.FXML;
import javafx.fxml.Initializable;
import javafx.geometry.Pos;
import javafx.scene.control.Accordion;
import javafx.scene.control.Button;
import javafx.scene.control.CheckBox;
import javafx.scene.control.ComboBox;
import javafx.scene.control.Label;
import javafx.scene.control.Slider;
import javafx.scene.control.TextField;
import javafx.scene.control.TitledPane;
import javafx.scene.layout.AnchorPane;
import javafx.scene.layout.GridPane;
import javafx.scene.layout.Pane;
import javafx.scene.layout.Region;
import javafx.scene.paint.Color;
import javafx.scene.text.Font;
import javafx.scene.text.FontWeight;

import org.controlsfx.control.TaskProgressView;
import org.controlsfx.dialog.Dialog;
import org.controlsfx.dialog.Dialogs;
import org.controlsfx.validation.ValidationSupport;
import org.controlsfx.validation.Validator;

import br.edu.ufam.dsverifier.domain.DigitalSystem;
import br.edu.ufam.dsverifier.domain.Implementation;
import br.edu.ufam.dsverifier.domain.Verification;
import br.edu.ufam.dsverifier.domain.enums.DigitalSystemProperties;
import br.edu.ufam.dsverifier.domain.enums.DigitalSystemRealizations;
import br.edu.ufam.dsverifier.domain.enums.VerificationStatus;
import br.edu.ufam.dsverifier.service.DSVerifierService;
import br.edu.ufam.dsverifier.util.DSVerifierUtils;

@SuppressWarnings("deprecation")
public class PrincipalController implements Initializable{
	
	@FXML
	private Accordion accordionPane;
	private TitledPane[] titledPanes;
	
	/* digital system */
	@FXML
	private TextField tfNumerator;
	@FXML
	private TextField tfDenominator;
	
	/* implementation */
	@FXML
	private Slider sliderIntegerBits;
	@FXML
	private Slider sliderPrecisionBits;
	@FXML
	private ComboBox<String> cbRealization;
	@FXML
	private Pane paneMinMax;
	
	/* properties */
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
	private AnchorPane taskPane;	
    private ExecutorService executorService = Executors.newFixedThreadPool(Runtime.getRuntime().availableProcessors());  
    private TaskProgressView<VerificationTask> taskProgressView;    
    private AtomicInteger finishedThreads = new AtomicInteger(0);
    public int totalThreads = 0;
    
    @FXML
    private Button btVerify;	
    @FXML
    private Button btSummary;
    
    List<Verification> verifications = null;
    
    ValidationSupport validationSupport = new ValidationSupport();
	
	@Override
	public void initialize(URL location, ResourceBundle resources) {
		
		Object[] panes = accordionPane.getPanes().toArray();
		titledPanes = Arrays.copyOf(panes, panes.length, TitledPane[].class);
		accordionPane.setExpandedPane(titledPanes[0]);
			
		/* add realizations */
		cbRealization.getItems().add(DigitalSystemRealizations.DFI.getRealization());
		cbRealization.getItems().add(DigitalSystemRealizations.DFII.getRealization());
		cbRealization.getItems().add(DigitalSystemRealizations.TDFII.getRealization());
		cbRealization.getItems().add(DigitalSystemRealizations.DDFI.getRealization());
		cbRealization.getItems().add(DigitalSystemRealizations.DDFII.getRealization());
		cbRealization.getItems().add(DigitalSystemRealizations.TDDFII.getRealization());
		cbRealization.getItems().add(DigitalSystemRealizations.CDFI.getRealization());
		cbRealization.getItems().add(DigitalSystemRealizations.CDFII.getRealization());
		cbRealization.getItems().add(DigitalSystemRealizations.CTDFII.getRealization());
		cbRealization.getItems().add(DigitalSystemRealizations.CDDFI.getRealization());
		cbRealization.getItems().add(DigitalSystemRealizations.CDDFII.getRealization());
		cbRealization.getItems().add(DigitalSystemRealizations.CTDDFII.getRealization());		
		
		/* set required fields */
        validationSupport.registerValidator(tfNumerator, Validator.createEmptyValidator("Digital System Numerator is Required"));	
        validationSupport.registerValidator(tfDenominator, Validator.createEmptyValidator("Digital System Denominator is Required"));        
        validationSupport.registerValidator(sliderIntegerBits, Validator.createEmptyValidator("Integer Bits of Implementation is Required"));	
        validationSupport.registerValidator(sliderPrecisionBits, Validator.createEmptyValidator("Precision Bits of Implementation is Required"));
        validationSupport.registerValidator(cbRealization, Validator.createEmptyValidator("Is necessary inform a Realization in Implementation"));              
        
        Region maxMinSlider = DSVerifierUtils.getInstance().createHorizontalSlider();
        paneMinMax.getChildren().add(maxMinSlider);
        taskProgressView = new TaskProgressView<VerificationTask>();
        taskProgressView.setMinWidth(760);
        taskPane.getChildren().add(taskProgressView);                     
        
	}
	
	public void verify() throws IOException, InterruptedException{
		
		verifications = validate();
		if (verifications == null || verifications.size() == 0) return;
		
		finishedThreads.set(0);
		totalThreads = verifications.size();
		btVerify.setDisable(true);
		for (Verification verification : verifications) {
			VerificationTask task = new VerificationTask(verification);		 
			 taskProgressView.getTasks().add(task);		 
			 executorService.submit(task);	
		}
		
	}
	
	public void reset(){
		btVerify.setDisable(false);
		btSummary.setDisable(true);
	}
	
	public void summary(){
	    Dialog dlg = new Dialog(null, "Verification Results",true);
	    
	    GridPane content = new GridPane();
	    content.setMinWidth(350);
	    content.setAlignment(Pos.CENTER);
	  
	    Label propertyLabel = new Label("Property                                        ");
	    propertyLabel.setFont(Font.font("Verdana", FontWeight.BOLD, 15));	    
	    Label timeLabel = new Label("Time(s)  ");
	    timeLabel.setFont(Font.font("Verdana", FontWeight.BOLD, 15));	    
	    Label resultLabel = new Label("Result");
	    resultLabel.setFont(Font.font("Verdana", FontWeight.BOLD, 15));
	    
	    content.add(propertyLabel, 0, 0);
	    content.add(timeLabel, 1, 0);
	    content.add(resultLabel, 2, 0);
	    
	    content.add(new Label(""), 0, 1);
	    content.add(new Label(""), 1, 1);
	    content.add(new Label(""), 2, 1);
	    
	    /* properties area */
	    int i=0;
	    for(i = 0; i < verifications.size(); i++){
		    content.add(new Label(verifications.get(i).getProperty().getName()), 0, i + 2);
		    content.add(new Label("-"), 1, i + 2);
		    if (verifications.get(i).getStatus() == VerificationStatus.VERIFICATION_SUCCESSFUL){
			    Label result = new Label("success");
			    result.setTextFill(Color.GREEN);
			    content.add(result, 2, i + 2);
		    }else if (verifications.get(i).getStatus() == VerificationStatus.VERIFICATION_FAILED){
		    	Label result = new Label("fail");
			    result.setTextFill(Color.RED);
			    content.add(result, 2, i + 2);
		    }
	    }
	    /* *************** */
	    
	    content.add(new Label(""), 0, i+2);
	    content.add(new Label(""), 1, i+2);
	    content.add(new Label(""), 2, i+2);
	    
	    dlg.setContent(content);
	    dlg.show();
	    
	}
	
	public void enableSummary(){
		if (totalThreads == finishedThreads.get()){
			btSummary.setDisable(false);
		}else{
			btSummary.setDisable(true);
		}
	}

	/**
	 * validate parameters and generate the list of verifications
	 * @throws IOException 
	 */
	public List<Verification> validate() throws IOException{
		
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
			DSVerifierService.getInstance().generateVerificationFile(verification);
			verifications.add(verification);
		}
		
		return verifications;
	}
	
	/* generate digital system */
	public DigitalSystem validateDigitalSystem(){
		
		String numerator = tfNumerator.getText();
		String denominator = tfDenominator.getText();

		if (numerator.length() == 0){
			accordionPane.setExpandedPane(titledPanes[0]);
			Dialogs.create()
		      .lightweight().styleClass(Dialog.STYLE_CLASS_UNDECORATED)
		      .message( "You need to input the digital system numerator")
		      .showWarning();
			tfNumerator.requestFocus();
			return null;
		}		
		int numeratorSize = numerator.split(",").length;
			
		if (denominator.length() == 0){
			accordionPane.setExpandedPane(titledPanes[0]);
			Dialogs.create()
		      .lightweight().styleClass(Dialog.STYLE_CLASS_UNDECORATED)
		      .message( "You need to input the digital system denominator")
		      .showWarning();
			tfDenominator.requestFocus();
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
				
		int integerBits = (int) sliderIntegerBits.getValue();
		int precisionBits = (int) sliderPrecisionBits.getValue();
		
		Implementation impl = new Implementation();
		impl.setIntegerBits(Integer.valueOf(integerBits));
		impl.setPrecisionBits(Integer.valueOf(precisionBits));	
		
		String realization = cbRealization.getValue();
		if (DigitalSystemRealizations.DFI.getRealization().equals(realization)){
			impl.setRealization(DigitalSystemRealizations.DFI);
		}else if (DigitalSystemRealizations.DFII.getRealization().equals(realization)){
			impl.setRealization(DigitalSystemRealizations.DFII);
		}else{
			accordionPane.setExpandedPane(titledPanes[1]);
			Dialogs.create()
		      .lightweight().styleClass(Dialog.STYLE_CLASS_UNDECORATED)
		      .message( "You need to select a realization")
		      .showWarning();
			return null;
		}
	
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
		if (checkMinimumPhase.isSelected())
			properties.add(DigitalSystemProperties.MINIMUM_PHASE);
		if (checkStability.isSelected())
			properties.add(DigitalSystemProperties.STABILITY);
		
		if (properties.size() == 0){
			accordionPane.setExpandedPane(titledPanes[2]);
			Dialogs.create()
		      .lightweight().styleClass(Dialog.STYLE_CLASS_UNDECORATED)
		      .message( "You need to select a property to check")
		      .showWarning();
			return null;
		}
		
		return properties;
	}
		
	class VerificationTask extends Task<Void> {
        
		private Verification verification;
		
        public VerificationTask(Verification verification) {
        	this.verification = verification;
            updateTitle("Checking " + verification.getProperty().getName()); 
        }
 
        @Override
        protected Void call() throws Exception { 
        	DSVerifierService.getInstance().callDSVerifier(verification);
        	finishedThreads.set(finishedThreads.get() + 1);   
        	enableSummary();
        	updateProgress(0, 0);
            done();
            return null;
        }
        
    }

}