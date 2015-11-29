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
import javafx.event.ActionEvent;
import javafx.event.EventHandler;
import javafx.fxml.FXML;
import javafx.fxml.Initializable;
import javafx.geometry.Pos;
import javafx.scene.control.Accordion;
import javafx.scene.control.Button;
import javafx.scene.control.CheckBox;
import javafx.scene.control.ComboBox;
import javafx.scene.control.Hyperlink;
import javafx.scene.control.Label;
import javafx.scene.control.Menu;
import javafx.scene.control.ScrollPane;
import javafx.scene.control.Slider;
import javafx.scene.control.Tab;
import javafx.scene.control.TextArea;
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
import br.edu.ufam.dsverifier.domain.SpaceState;
import br.edu.ufam.dsverifier.domain.Verification;
import br.edu.ufam.dsverifier.domain.enums.DigitalSystemProperties;
import br.edu.ufam.dsverifier.domain.enums.DigitalSystemRealizations;
import br.edu.ufam.dsverifier.domain.enums.VerificationStatus;
import br.edu.ufam.dsverifier.service.DSVerifierService;
import br.edu.ufam.dsverifier.service.DSVerifierSpaceStateService;
import br.edu.ufam.dsverifier.util.DSVerifierConstants;
import br.edu.ufam.dsverifier.util.DSVerifierUtils;
import br.edu.ufam.dsverifier.util.DialogControllerUtils;
import br.edu.ufam.dsverifier.util.FileUtils;
import br.edu.ufam.dsverifier.util.SpaceStateUtils;

@SuppressWarnings("deprecation")
public class PrincipalController implements Initializable {

	@FXML
	private Accordion accordionPaneDS;
	private TitledPane[] titledPanes;
	@FXML
	private ScrollPane scrollPaneDS;

	@FXML
	private Tab tabDigitalSystem;
	@FXML
	private Tab tabSpaceState;
	
	/* digital system */
	@FXML
	private TextField tfNumerator;
	@FXML
	private TextField tfDenominator;
	
	/* digital system (control) */
	@FXML
	private TextField tfNumeratorControl;
	@FXML
	private TextField tfDenominatorControl;
	
	/* digital system (plant) */
	@FXML
	private TextField tfNumeratorPlant;
	@FXML
	private TextField tfDenominatorPlant;
	

	/* implementation */
	@FXML
	private Slider sliderIntegerBits;
	@FXML
	private Slider sliderPrecisionBits;
	@FXML
	private ComboBox<String> cbRealization;
	@FXML
	private Pane paneMinMax;
	@FXML
	private TextField tfDelta;
	@FXML
	private TextField tfScale;

	/* properties */
	@FXML
	private CheckBox checkOverflow;
	@FXML
	private CheckBox checkLimitCycle;
	@FXML
	private CheckBox checkZeroInputLimitCycle;
	@FXML
	private CheckBox checkStabilityClosedLoop;
	@FXML
	private CheckBox checkTiming;	

	@FXML
	private CheckBox checkError;
	@FXML
	private CheckBox checkStability;
	@FXML
	private CheckBox checkMinimumPhase;

	@FXML
	private Slider sliderBound;

	@FXML
	private AnchorPane taskPane;
	public static ExecutorService executorService = Executors
			.newFixedThreadPool(Runtime.getRuntime().availableProcessors());
	private TaskProgressView<VerificationTask> taskProgressView;
	private final AtomicInteger finishedThreads = new AtomicInteger(0);
	public int totalThreads = 0;

	@FXML
	private Button btVerify;
	@FXML
	private Button btSummary;

	@FXML
	private Menu menuBenchmarks;

	List<Verification> verifications = null;
	ValidationSupport validationSupport = new ValidationSupport();

	private TextField tfMax;
	private TextField tfMin;

	/**
	 * Space States fields
	 */
	
	@FXML
	private Slider sliderIntegerBitsSpaceState;
	@FXML
	private Slider sliderPrecisionBitsSpaceState;
	@FXML
	private Button btVerifySpaceState;
	@FXML
	private Button btSummarySpaceState;
	@FXML
	private AnchorPane taskPaneSpaceState;
	@FXML
	private Slider sliderBoundSpaceState;
	@FXML
	private CheckBox checkStabilitySpaceState;
	@FXML
	private CheckBox checkQuantisationError;
	@FXML
	private CheckBox checkStabilityClosedLoopSpaceState;
	@FXML
	private TextField errorLimit;
	@FXML
	private TextField stateVariables;
	@FXML
	private TextField inputs;
	@FXML
	private TextField outputs;
	@FXML
	private Button btGenerateValues;
	@FXML
	private Label labelErrorLimit;
	@FXML
	private Accordion accordionPaneSS;
	private TitledPane[] titledPanesSS;
	private TaskProgressView<VerificationSpaceStateTask> taskProgressSSView;
	@Override
	public void initialize(final URL location, final ResourceBundle resources) {

		final Object[] panesDS = accordionPaneDS.getPanes().toArray();
		titledPanes = Arrays.copyOf(panesDS, panesDS.length, TitledPane[].class);
		accordionPaneDS.setExpandedPane(titledPanes[0]);
		
		final Object[] panesSS = accordionPaneSS.getPanes().toArray();
		titledPanesSS = Arrays.copyOf(panesSS, panesSS.length, TitledPane[].class);
		accordionPaneSS.setExpandedPane(titledPanesSS[0]);
		
		setRealizationsItems();
		setRequiredFields();
	}

	private void setRealizationsItems() {
		/* add realizations */
		cbRealization.getItems().add(DigitalSystemRealizations.DFI.getRealization());
		cbRealization.getItems().add(DigitalSystemRealizations.DFII.getRealization());
		cbRealization.getItems().add(DigitalSystemRealizations.TDFII.getRealization());
		cbRealization.getItems().add(DigitalSystemRealizations.DDFI.getRealization());
		cbRealization.getItems().add(DigitalSystemRealizations.DDFII.getRealization());
		cbRealization.getItems().add(DigitalSystemRealizations.TDDFII.getRealization());

		/*
		 * cbRealization.getItems().add(DigitalSystemRealizations.CDFI.
		 * getRealization());
		 * cbRealization.getItems().add(DigitalSystemRealizations
		 * .CDFII.getRealization());
		 * cbRealization.getItems().add(DigitalSystemRealizations
		 * .CTDFII.getRealization());
		 * cbRealization.getItems().add(DigitalSystemRealizations
		 * .CDDFI.getRealization());
		 * cbRealization.getItems().add(DigitalSystemRealizations
		 * .CDDFII.getRealization());
		 * cbRealization.getItems().add(DigitalSystemRealizations
		 * .CTDDFII.getRealization());
		 */
	}

	private void setRequiredFields() {
		/* set required fields */
        validationSupport.registerValidator(tfNumerator, Validator.createEmptyValidator("Digital System Numerator is Required"));	
        validationSupport.registerValidator(tfDenominator, Validator.createEmptyValidator("Digital System Denominator is Required"));        
        validationSupport.registerValidator(tfNumeratorControl, Validator.createEmptyValidator("Control Numerator is Required"));	
        validationSupport.registerValidator(tfDenominatorControl, Validator.createEmptyValidator("Control Denominator is Required"));
        validationSupport.registerValidator(tfNumeratorPlant, Validator.createEmptyValidator("Control Numerator is Required"));	
        validationSupport.registerValidator(tfDenominatorPlant, Validator.createEmptyValidator("Control Denominator is Required"));        
        validationSupport.registerValidator(sliderIntegerBits, Validator.createEmptyValidator("Integer Bits of Implementation is Required"));	
        validationSupport.registerValidator(sliderPrecisionBits, Validator.createEmptyValidator("Precision Bits of Implementation is Required"));
        validationSupport.registerValidator(cbRealization, Validator.createEmptyValidator("Is necessary inform a Realization in Implementation"));              
		validationSupport.registerValidator(stateVariables,Validator.createEmptyValidator("Is necessary inform a n state variables in Implementation"));
		validationSupport.registerValidator(inputs,Validator.createEmptyValidator("Is necessary inform a p inputs in Implementation"));
		validationSupport.registerValidator(outputs,Validator.createEmptyValidator("Is necessary inform a q outputs in Implementation"));
		validationSupport.registerValidator(errorLimit,Validator.createEmptyValidator("Is necessary inform the error limit in Implementation"));
		validationSupport.registerValidator(sliderIntegerBitsSpaceState,Validator.createEmptyValidator("Integer Bits of Implementation is Required"));
		validationSupport.registerValidator(sliderPrecisionBitsSpaceState,Validator.createEmptyValidator("Precision Bits of Implementation is Required"));

		tfMax = new TextField();
        tfMin = new TextField();        
        final Region maxMinSlider = DSVerifierUtils.getInstance().createHorizontalSlider(tfMin, tfMax);
        paneMinMax.getChildren().add(maxMinSlider);
        taskProgressView = new TaskProgressView<VerificationTask>();
        taskProgressView.setMinWidth(760);
        taskPane.getChildren().add(taskProgressView);      
        
        taskProgressSSView = new TaskProgressView<VerificationSpaceStateTask>();
        taskProgressSSView.setMinWidth(760);
        taskPaneSpaceState.getChildren().add(taskProgressSSView);    

	}

	public void generateSpaceStateValues() {
		final int pInputs, qOutputs, nStates;
		
		pInputs = SpaceStateUtils.parserFieldInteger(inputs);
		qOutputs = SpaceStateUtils.parserFieldInteger(outputs);
		nStates = SpaceStateUtils.parserFieldInteger(stateVariables);

		if (SpaceStateUtils.validateSpaceStateConstants(pInputs, qOutputs,
				nStates)) {
			DialogControllerUtils.showDialogSpaceState(pInputs, qOutputs,
					nStates, checkStabilityClosedLoopSpaceState.isSelected());
		} else {
			accordionPaneDS.setExpandedPane(titledPanes[0]);
			Dialogs.create().lightweight()
					.styleClass(Dialog.STYLE_CLASS_UNDECORATED)
					.message(DSVerifierConstants.MSG_ERROR_VALUES)
					.showWarning();
		}

	}

	public void verify() throws IOException, InterruptedException {

		if (tabSpaceState.isSelected()) {
			verifySpaceState();
		} else if (tabDigitalSystem.isSelected()){
			verifyDigitalSystem();
		} else {
			DialogControllerUtils.showDialogErrorInputValues(accordionPaneDS,titledPanes);
		}
	}

	private void verifyDigitalSystem() throws IOException {

		verifications = validate();
		if (verifications == null || verifications.size() == 0)
			return;

		finishedThreads.set(0);
		totalThreads = verifications.size();
		btVerify.setDisable(true);
		for (final Verification verification : verifications) {
			final VerificationTask task = new VerificationTask(verification);
			taskProgressView.getTasks().add(task);
			executorService.submit(task);
		}
	}

	public void resetDigitalSystem() {
		btVerify.setDisable(false);
		btSummary.setDisable(true);
	}
	
	public void resetSpaceState() {
		btVerifySpaceState.setDisable(false);
		btSummarySpaceState.setDisable(true);
	}

	public void summary() {

		final Dialog dlgSummary = new Dialog(null, "Verification Results", true);

		final GridPane content = new GridPane();
		content.setMinWidth(350);
		content.setAlignment(Pos.CENTER);

		final Label propertyLabel = new Label(
				"Property                                        ");
		propertyLabel.setFont(Font.font("Verdana", FontWeight.BOLD, 15));
		final Label timeLabel = new Label("Time(s)  ");
		timeLabel.setFont(Font.font("Verdana", FontWeight.BOLD, 15));
		final Label resultLabel = new Label("Result      ");
		resultLabel.setFont(Font.font("Verdana", FontWeight.BOLD, 15));

		content.add(propertyLabel, 0, 0);
		content.add(timeLabel, 1, 0);
		content.add(resultLabel, 2, 0);

		content.add(new Label(""), 0, 1);
		content.add(new Label(""), 1, 1);
		content.add(new Label(""), 2, 1);

		/* properties area */
		int i = 0;
		for (i = 0; i < verifications.size(); i++) {
			final Verification verification = verifications.get(i);
			content.add(new Label(verification.getProperty().getName()), 0,
					i + 2);
			content.add(new Label(verification.getTime().toString()), 1, i + 2);
			if (verification.getStatus() == VerificationStatus.VERIFICATION_SUCCESSFUL) {
				final Label result = new Label("success");
				result.setTextFill(Color.GREEN);
				content.add(result, 2, i + 2);
			} else if (verification.getStatus() == VerificationStatus.VERIFICATION_FAILED) {
				final Label result = new Label("fail");
				result.setTextFill(Color.RED);
				content.add(result, 2, i + 2);

				final Hyperlink viewCE = new Hyperlink("Counter\nExample");

				viewCE.setOnAction(new EventHandler<ActionEvent>() {
					@Override
					public void handle(final ActionEvent event) {
						showCounterExample(verification);
					}
				});
				content.add(viewCE, 3, i + 2);

				final Hyperlink viewInputs = new Hyperlink("Show\nInputs");
				viewInputs.setOnAction(new EventHandler<ActionEvent>() {
					@Override
					public void handle(final ActionEvent event) {
						try {
							DialogControllerUtils.showInputs(verification);
						} catch (final IOException e) {
							e.printStackTrace();
						}
					}
				});
				content.add(viewInputs, 4, i + 2);

			} else if (verification.getStatus() == VerificationStatus.UNKNOWN) {
				final Label result = new Label("unknown");
				result.setTextFill(Color.YELLOW);
				content.add(result, 2, i + 2);
			}
		}
		/* *************** */

		content.add(new Label(""), 0, i + 2);
		content.add(new Label(""), 1, i + 2);
		content.add(new Label(""), 2, i + 2);

		dlgSummary.setContent(content);
		dlgSummary.show();

	}

	public void enableSummary() {

		if (totalThreads == finishedThreads.get()) {
			btSummary.setDisable(false);
		} else {
			btSummary.setDisable(true);
		}

	}
	
	public void enableSummarySpaceState() {

		if (totalThreads == finishedThreads.get()) {
			btSummarySpaceState.setDisable(false);
		} else {
			btSummarySpaceState.setDisable(true);
		}

	}


	public void showCounterExample(final Verification verification) {

		final Dialog dlg = new Dialog(null, "Counterexample for "
				+ verification.getProperty().getName() + " Verification", true);
		final TextArea t = new TextArea();
		t.setText(verification.getOutput());
		t.setMinHeight(400);
		t.setMaxHeight(400);
		t.setMinWidth(800);
		t.setMaxWidth(800);
		t.setEditable(false);
		dlg.setContent(t);
		dlg.show();

	}

	/**
	 * validate parameters and generate the list of verifications
	 * 
	 * @throws IOException
	 */
	public List<Verification> validate() throws IOException {

		/* digital systems check */
		DigitalSystem ds = null;
		DigitalSystem control = null;
		DigitalSystem plant = null;
		if (!isClosedLoopVerification()) {
			ds = validateDigitalSystem();
			if (ds == null)
				return null;
		} else {
			control = validateControlDigitalSystem();
			if (control == null)
				return null;
			plant = validatePlantDigitalSystem();
			if (plant == null)
				return null;
		}

		/* implementation */
		final Implementation impl  = validateImplementation();
		if (impl == null)
			return null;
		/* prepare a list of properties to check */
		final Set<DigitalSystemProperties> properties = validateProperties();
		if (properties == null)
			return null;

		/* create the verification list */
		final List<Verification> verifications = new ArrayList<Verification>();
		
		if (isClosedLoopVerification()) {
			/* closedloop verification */
			final Verification cloopVerification = new Verification();
			cloopVerification.setPlant(plant);
			cloopVerification.setControl(plant);
			cloopVerification.setImplementation(impl);
			DSVerifierService.getInstance().generateClosedLoopVerificationFile(
					cloopVerification);
			cloopVerification
					.setProperty(DigitalSystemProperties.STABILITY_CLOSED_LOOP);
			cloopVerification.setBound(1);
			verifications.add(cloopVerification);
		} else {
			for (final DigitalSystemProperties property : properties) {
				final Verification verification = new Verification();
				verification.setDigitalSystem(ds);
				verification.setImplementation(impl);
				verification.setProperty(property);
				DSVerifierService.getInstance().generateVerificationFile(
						verification);
				verification.setBound((int) sliderBound.getValue());
				verifications.add(verification);
			}
		}

		return verifications;
	}
	

	
	public boolean isClosedLoopVerification(){
		return checkStabilityClosedLoop.isSelected();
	}
	
	/* generate digital system */
	public DigitalSystem validateDigitalSystem(){
				
		final String numerator = tfNumerator.getText();
		final String denominator = tfDenominator.getText();

		if (numerator.length() == 0){
			accordionPaneDS.setExpandedPane(titledPanes[0]);
			Dialogs.create()
		      .lightweight().styleClass(Dialog.STYLE_CLASS_UNDECORATED)
		      .message( "You need to input the digital system numerator")
		      .showWarning();
			tfNumerator.requestFocus();
			return null;
		}		
		final int numeratorSize = numerator.split(",").length;
			
		if (denominator.length() == 0){
			accordionPaneDS.setExpandedPane(titledPanes[0]);
			Dialogs.create()
		      .lightweight().styleClass(Dialog.STYLE_CLASS_UNDECORATED)
		      .message( "You need to input the digital system denominator")
		      .showWarning();
			tfDenominator.requestFocus();
			return null;
		}
		final int denominatorSize = denominator.split(",").length;

		final DigitalSystem ds =  new DigitalSystem();
		ds.setNumerator(numerator);
		ds.setNumeratorSize(numeratorSize);
		ds.setDenominator(denominator);
		ds.setDenominatorSize(denominatorSize);

		return ds;
	}
	
	/* generate digital system */
	public DigitalSystem validateControlDigitalSystem(){
				
		final String numerator = tfNumeratorControl.getText();
		final String denominator = tfDenominatorControl.getText();

		if (numerator.length() == 0){
			accordionPaneDS.setExpandedPane(titledPanes[1]);
			Dialogs.create()
		      .lightweight().styleClass(Dialog.STYLE_CLASS_UNDECORATED)
		      .message( "You need to input the control numerator")
		      .showWarning();
			tfNumeratorControl.requestFocus();
			return null;
		}		
		final int numeratorSize = numerator.split(",").length;
			
		if (denominator.length() == 0){
			accordionPaneDS.setExpandedPane(titledPanes[1]);
			Dialogs.create()
		      .lightweight().styleClass(Dialog.STYLE_CLASS_UNDECORATED)
		      .message( "You need to input the control denominator")
		      .showWarning();
			tfDenominatorControl.requestFocus();
			return null;
		}
		final int denominatorSize = denominator.split(",").length;

		final DigitalSystem ds =  new DigitalSystem();
		ds.setNumerator(numerator);
		ds.setNumeratorSize(numeratorSize);
		ds.setDenominator(denominator);
		ds.setDenominatorSize(denominatorSize);

		return ds;
	}
	
	/* generate digital system */
	public DigitalSystem validatePlantDigitalSystem(){
				
		final String numerator = tfNumeratorPlant.getText();
		final String denominator = tfDenominatorPlant.getText();

		if (numerator.length() == 0){
			accordionPaneDS.setExpandedPane(titledPanes[1]);
			Dialogs.create()
		      .lightweight().styleClass(Dialog.STYLE_CLASS_UNDECORATED)
		      .message( "You need to input the plant numerator")
		      .showWarning();
			tfNumeratorPlant.requestFocus();
			return null;
		}		
		final int numeratorSize = numerator.split(",").length;
			
		if (denominator.length() == 0){
			accordionPaneDS.setExpandedPane(titledPanes[1]);
			Dialogs.create()
		      .lightweight().styleClass(Dialog.STYLE_CLASS_UNDECORATED)
		      .message( "You need to input the plant denominator")
		      .showWarning();
			tfDenominatorPlant.requestFocus();
			return null;
		}
		final int denominatorSize = denominator.split(",").length;

		final DigitalSystem ds =  new DigitalSystem();
		ds.setNumerator(numerator);
		ds.setNumeratorSize(numeratorSize);
		ds.setDenominator(denominator);
		ds.setDenominatorSize(denominatorSize);

		return ds;
	}
	/* generate implementation */
	public Implementation validateImplementation() {

		final int integerBits = (int) sliderIntegerBits.getValue();
		final int precisionBits = (int) sliderPrecisionBits.getValue();

		final Implementation impl = new Implementation();
		impl.setIntegerBits(Integer.valueOf(integerBits));
		impl.setPrecisionBits(Integer.valueOf(precisionBits));

		final String realization = cbRealization.getValue();
		if (DigitalSystemRealizations.DFI.getRealization().equals(realization)) {
			impl.setRealization(DigitalSystemRealizations.DFI);
		} else if (DigitalSystemRealizations.DFII.getRealization().equals(
				realization)) {
			impl.setRealization(DigitalSystemRealizations.DFII);
		} else if (DigitalSystemRealizations.TDFII.getRealization().equals(
				realization)) {
			impl.setRealization(DigitalSystemRealizations.TDFII);
		} else if (DigitalSystemRealizations.DDFI.getRealization().equals(
				realization)) {
			impl.setRealization(DigitalSystemRealizations.DDFI);
		} else if (DigitalSystemRealizations.DDFII.getRealization().equals(
				realization)) {
			impl.setRealization(DigitalSystemRealizations.DDFII);
		} else if (DigitalSystemRealizations.TDDFII.getRealization().equals(
				realization)) {
			impl.setRealization(DigitalSystemRealizations.TDDFII);
		} else if (DigitalSystemRealizations.CDFI.getRealization().equals(
				realization)) {
			impl.setRealization(DigitalSystemRealizations.CDFI);
		} else if (DigitalSystemRealizations.CDFII.getRealization().equals(
				realization)) {
			impl.setRealization(DigitalSystemRealizations.CDFII);
		} else if (DigitalSystemRealizations.CTDFII.getRealization().equals(
				realization)) {
			impl.setRealization(DigitalSystemRealizations.CTDFII);
		} else if (DigitalSystemRealizations.CDDFI.getRealization().equals(
				realization)) {
			impl.setRealization(DigitalSystemRealizations.CDDFI);
		} else if (DigitalSystemRealizations.CDDFII.getRealization().equals(
				realization)) {
			impl.setRealization(DigitalSystemRealizations.CDDFII);
		} else if (DigitalSystemRealizations.CTDDFII.getRealization().equals(realization)){
			impl.setRealization(DigitalSystemRealizations.CTDDFII);	
		} else{
			accordionPaneDS.setExpandedPane(titledPanes[2]);
			Dialogs.create()
		      .lightweight().styleClass(Dialog.STYLE_CLASS_UNDECORATED)
		      .message( "You need to select a realization")
		      .showWarning();

			return null;
		}

		/* check if requires a delta value */

		if ((impl.getRealization() == DigitalSystemRealizations.DDFI)    ||
		    (impl.getRealization() == DigitalSystemRealizations.DDFII)   || 		   
		    (impl.getRealization() == DigitalSystemRealizations.TDDFII)  ||
			(impl.getRealization() == DigitalSystemRealizations.CDDFI)   ||
		    (impl.getRealization() == DigitalSystemRealizations.CDDFII)  || 		   
		    (impl.getRealization() == DigitalSystemRealizations.CTDDFII)) {
			if (tfDelta.getText().length() == 0){
				accordionPaneDS.setExpandedPane(titledPanes[2]);
				Dialogs.create()
			      .lightweight().styleClass(Dialog.STYLE_CLASS_UNDECORATED)
			      .message( "You need to inform a delta value")
			      .showWarning();
				return null;
			}
			Double delta;
			if ((delta = DSVerifierUtils.getInstance().isNumeric(tfDelta.getText())) == null){
				accordionPaneDS.setExpandedPane(titledPanes[2]);
				Dialogs.create()
			      .lightweight().styleClass(Dialog.STYLE_CLASS_UNDECORATED)
			      .message("Delta value needs to be a number")
			      .showError();

				return null;
			}
			impl.setDelta(delta);
		}

		impl.setMaximum(Double.valueOf(tfMax.getText()));
		impl.setMinimum(Double.valueOf(tfMin.getText()));			
		
		if (tfScale.getText().length() == 0){
			accordionPaneDS.setExpandedPane(titledPanes[2]);
			Dialogs.create()
		      .lightweight().styleClass(Dialog.STYLE_CLASS_UNDECORATED)
		      .message( "You need to inform a scaling factor")
		      .showWarning();
			return null;
		}
		Double scale;
		if ((scale = DSVerifierUtils.getInstance().isNumeric(tfScale.getText())) == null) {
			accordionPaneDS.setExpandedPane(titledPanes[2]);
			Dialogs.create().lightweight()
					.styleClass(Dialog.STYLE_CLASS_UNDECORATED)
					.message("Scale value needs to be a number").showError();
			return null;
		} else {
			impl.setScale(scale.longValue());
		}

		return impl;
	}
	
	public void openAbout() {
		final ShowAboutDialogController showSpaceStateDialog = new ShowAboutDialogController();
		showSpaceStateDialog.show();
	}

	public void openBenchmarks() {
		Main.application.getHostServices().showDocument(
				"http://www.dsverifier.org/benchmarks");
	}

	public void openDocumentation() {
		Main.application.getHostServices().showDocument(
				"http://www.dsverifier.org/documentation");
	}

	public void openPublications() {
		Main.application.getHostServices().showDocument(
				"http://www.dsverifier.org/publications");
	}

	/* generate properties to check */
	public Set<DigitalSystemProperties> validateProperties() {

		final Set<DigitalSystemProperties> properties = new HashSet<DigitalSystemProperties>();
		if (checkOverflow.isSelected())
			properties.add(DigitalSystemProperties.OVERFLOW);
		if (checkLimitCycle.isSelected())
			properties.add(DigitalSystemProperties.LIMIT_CYCLE);
		if (checkZeroInputLimitCycle.isSelected())
			properties.add(DigitalSystemProperties.ZERO_INPUT_LIMIT_CYCLE);
		if (checkTiming.isSelected())
			properties.add(DigitalSystemProperties.TIMING);
		if (checkMinimumPhase.isSelected())
			properties.add(DigitalSystemProperties.MINIMUM_PHASE);
		if (checkStability.isSelected())
			properties.add(DigitalSystemProperties.STABILITY);
		if (checkStabilityClosedLoop.isSelected())
			properties.add(DigitalSystemProperties.STABILITY_CLOSED_LOOP);
		
		if (properties.size() == 0){
			accordionPaneDS.setExpandedPane(titledPanes[3]);
			Dialogs.create()
		      .lightweight().styleClass(Dialog.STYLE_CLASS_UNDECORATED)
		      .message( "You need to select a property to check")
		      .showWarning();

			return null;
		}

		return properties;
	}

	class VerificationTask extends Task<Void> {

		private final Verification verification;

		public VerificationTask(final Verification verification) {
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
	
	class VerificationSpaceStateTask extends Task<Void> {

		private final Verification verification;

		public VerificationSpaceStateTask(final Verification verification) {
			this.verification = verification;
			updateTitle("Checking " + verification.getProperty().getName());
		}

		@Override
		protected Void call() throws Exception {
			DSVerifierSpaceStateService.getInstance().callDSVerifier(verification);
			finishedThreads.set(finishedThreads.get() + 1);
			enableSummarySpaceState();
			updateProgress(0, 0);
			done();
			return null;
		}

	}
	
	private void verifySpaceState() throws IOException{
		verifications = validateSpaceState();
		if (verifications == null || verifications.size() == 0)
			return;

		finishedThreads.set(0);
		totalThreads = verifications.size();
		btVerifySpaceState.setDisable(true);
		for (final Verification verification : verifications) {
			final VerificationSpaceStateTask task = new VerificationSpaceStateTask(verification);
			taskProgressSSView.getTasks().add(task);
			executorService.submit(task);
		}	
	}
	
	private List<Verification> validateSpaceState() throws IOException{
		double errorLimitValue = 0;
		
		/* prepare a list of properties to check */
		final Set<DigitalSystemProperties> properties = validatePropertiesSpaceSate();
		if (properties == null)
			return null;
		
		final Implementation implementation = validateImplementationSpaceState();
		if (implementation == null)
			return null;
		
		if (checkQuantisationError.isSelected()
				&& errorLimit.getText().isEmpty()) {
			accordionPaneSS.setExpandedPane(titledPanesSS[2]);
			Dialogs.create().lightweight()
					.styleClass(Dialog.STYLE_CLASS_UNDECORATED)
					.message("You need to set a value for Error Limit")
					.showWarning();

			return null;
		} else if (checkQuantisationError.isSelected()){
			errorLimitValue = Double.parseDouble(errorLimit.getText().toString());
		}

		/* create the verification list */
		final List<Verification> verifications = new ArrayList<Verification>();
		
		if (SpaceStateUtils.isValidSpaceStateInputs(inputs, outputs, stateVariables)) {

			if (FileUtils.isFileExists(DSVerifierConstants.FILE_TEMP_SS)
					&& !FileUtils.isFileExists(DSVerifierConstants.FILE_SS)) {
			
				SpaceStateUtils.getInstance().createVerificationSpaceStateFile(
						(int) sliderIntegerBitsSpaceState.getValue(),
						(int) sliderPrecisionBitsSpaceState.getValue(), errorLimitValue, checkStabilityClosedLoopSpaceState.isSelected());
				verifySpaceState(properties, verifications, implementation, errorLimitValue);
			
			} else if (FileUtils.isFileExists(DSVerifierConstants.FILE_SS)) {
				if (SpaceStateUtils.isStateSpaceInputsChanged(
						stateVariables, inputs, outputs, checkStabilityClosedLoopSpaceState)) {
					DialogControllerUtils
							.showDialogErrorMatrixChangedValues(
									accordionPaneSS, titledPanesSS);
					return null;
				} else {
					verifySpaceState(properties, verifications, implementation, errorLimitValue);
				}
			} else {
				DialogControllerUtils.showDialogErrorMatrixValues(
						accordionPaneSS, titledPanesSS);
				return null;
			}
		} else {
			DialogControllerUtils.showDialogErrorStateConstantsValues(
					accordionPaneSS, titledPanesSS);
			return null;
		}
		
		return verifications;
	}

	private Implementation validateImplementationSpaceState() {
		final int integerBits = (int) sliderIntegerBits.getValue();
		final int precisionBits = (int) sliderPrecisionBits.getValue();

		final Implementation impl = new Implementation();
		impl.setIntegerBits(Integer.valueOf(integerBits));
		impl.setPrecisionBits(Integer.valueOf(precisionBits));
		
		return impl;
	}

	private void verifySpaceState(final Set<DigitalSystemProperties> properties,
			final List<Verification> verifications, final Implementation implemenation, final double errorLimitValue) {
		final SpaceState spaceState = DSVerifierSpaceStateService.getInstance().getSpaceState();
		spaceState.setErrorLimit(errorLimitValue);
		spaceState.setClosedLoop(false);
		
		if (checkStabilityClosedLoopSpaceState.isSelected()) {
			spaceState.setClosedLoop(true);
		}
		
		DialogControllerUtils.showDialogStartingVerification(accordionPaneDS, titledPanes);
		/* create the verification list */
		for (final DigitalSystemProperties property : properties) {
			final Verification verification = new Verification();
			verification.setProperty(property);
			verification.setImplementation(implemenation);
			verification.setSpaceState(spaceState);
			DSVerifierSpaceStateService.getInstance().generateSpaceStateVerificationFile(
					verification);
			verification.setBound((int) sliderBoundSpaceState.getValue());
			verifications.add(verification);
		}
	}
	
	/* generate properties to check */
	public Set<DigitalSystemProperties> validatePropertiesSpaceSate() {

		final Set<DigitalSystemProperties> properties = new HashSet<DigitalSystemProperties>();

		if (checkStabilitySpaceState.isSelected())
			properties.add(DigitalSystemProperties.STABILITY);
		if (checkQuantisationError.isSelected())
			properties.add(DigitalSystemProperties.QUANTISATION_ERROR);
		
		if (properties.size() == 0){
			accordionPaneSS.setExpandedPane(titledPanesSS[2]);
			Dialogs.create()
		      .lightweight().styleClass(Dialog.STYLE_CLASS_UNDECORATED)
		      .message( "You need to select a property to check")
		      .showWarning();

			return null;
		}

		return properties;
	}
	
	public void closeDSVerifier() throws Throwable{
		this.finalize();
	}
	
	public void isSpaceStateClosedLoop(){
		if(checkQuantisationError.isSelected()){
			labelErrorLimit.setVisible(true);
			errorLimit.setVisible(true);
		} else {
			labelErrorLimit.setVisible(false);
			errorLimit.setVisible(false);
		}
	}
	
}