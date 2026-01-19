# 🌍 WebGIS - 지능형 2D/3D 지도 서비스

![WebGIS Preview](https://img.shields.io/badge/WebGIS-Modern_Design-blue?style=for-the-badge)
![Tech Stack](https://img.shields.io/badge/OpenLayers-MapLibre_GL-brightgreen?style=for-the-badge)

사용자 친화적인 인터페이스와 강력한 분석 기능을 갖춘 오픈소스 기반의 웹 지도 서비스입니다. 2D 지도의 정밀한 측정 기능부터 3D 지도의 실감 나는 탐색까지, 다양한 지리정보 시스템(GIS) 기능을 웹 브라우저에서 즉시 경험할 수 있습니다.

---

## ✨ 핵심 기능

### 1. 🗺️ 하이브리드 지도 모드 (2D & 3D)
*   **2D 모드**: OpenLayers 기반의 빠르고 정확한 벡터/위성/지형도 레이어 제공.
*   **3D 모드**: MapLibre GL 기술을 활용한 입체 건물 투영 및 지형 렌더링.
*   **심리스 전환**: 헤더의 레이어 선택기를 통해 2D와 3D 모드를 즉시 전환 가능.

### 2. 📏 스마트 측정 도구
*   **거리 및 면적 측정**: 고도화된 지오데식(Geodesic) 계산법을 적용하여 지구의 곡률을 반영한 정확한 수치 계산.
*   **실시간 배지**: 측정 중 각 선분의 길이와 방위각을 툴팁과 배지로 즉시 표시.
*   **측정 이력 관리**: 과거 측정 데이터가 자동으로 저장되며, 언제든 다시 확인하거나 삭제 가능.

### 3. 🚗 지능형 경로 탐색 (Navigation)
*   **다중 모드**: 자동차, 도보, 자전거 경로 탐색 지원.
*   **실시간 위치 추적**: GPS 연동을 통해 지도상에 내 위치를 실시간으로 표시하고 경로를 재계산.
*   **POI 연동**: 지도상의 특정 장소(가게, 역 등)를 클릭하여 즉시 목적지로 설정 가능.

### 4. 🖼️ AI 이미지 위치 분석 (GeoSpy Style)
*   **이미지 기반 검색**: 사진을 업로드하면 GPS 메타데이터 또는 AI 시각 분석(랜드마크, OCR)을 통해 사진이 찍힌 위치를 추정하여 지도에 표시.
*   **위치 기반 이미지 탐색**: 지도를 클릭하면 해당 위치 주변의 실제 사진과 관련 뉴스/소식을 갤러리 형태로 제공.

### 5. 🏢 상세 POI(장소) 정보
*   **심층 데이터 매칭**: 단순한 이름 표시를 넘어 전화번호, 영업시간, 상세 주소, 메뉴/종류, 공식 홈페이지 및 SNS(인스타그램, 페이스북) 링크 제공.
*   **스마트 필터링**: 무의미한 태그 대신 실제 건물 이름과 브랜드 명칭을 정확히 식별하여 표시.

### 6. 🌓 프리미엄 디자인 및 테마
*   **반응형 UI**: 데스크탑부터 모바일 기기까지 최적화된 화면 구성.
*   **스마트 사이드바**: 아코디언 메뉴 시스템을 적용하여, 사용하는 도구에 따라 관련 패널이 자동으로 나타나고 숨겨짐.
*   **다크 모드**: 시력 보호와 디자인 미학을 위한 완벽한 다크 테마 지원.

---

## 🛠️ 기술 스택
*   **Frontend**: HTML5, CSS3 (Vanilla CSS), JavaScript (Vanilla JS)
*   **Map Engine**: [OpenLayers](https://openlayers.org/) (2D), [MapLibre GL JS](https://maplibre.org/) (3D)
*   **Server**: [Node.js](https://nodejs.org/) (Data Proxy & Server-side tasks)
*   **API 연동**:
    *   **Search/Geocoding**: Nominatim (OpenStreetMap)
    *   **Routing**: OSRM (Open Source Routing Machine)
    *   **Street View**: 오픈소스 Mapillary 연동 서비스 제공.
    *   **Images**: Flickr API & Wikipedia

---

## 🚀 시작하기

### 설치 및 실행
1.  저장소를 클론합니다.
    ```bash
    git clone https://github.com/USER/WebGIS.git
    ```
2.  의존성 패키지를 설치합니다.
    ```bash
    npm install
    ```
3.  개발 서버를 실행합니다.
    ```bash
    npm run dev    # 프론트엔드 (Vite)
    npm run server # 백엔드 프록시 서버
    ```

---

## 📂 프로젝트 구조
*   `index.html`: 서비스의 메인 구조 및 레이아웃.
*   `main.js`: 지도 로직, 이벤트 핸들링, API 연동 등 핵심 기능 구현.
*   `styles.css`: 프리미엄 디자인 시스템 및 테마 스타일 정의.
*   `server/`: API 프록시 및 대용량 데이터 처리를 위한 서버 로직.

---

## 📝 라이선스
이 프로젝트는 오픈소스 프로젝트로 제공되지만, 모든 권한은 **H2aler**에게 있습니다. 상세한 정보는 LICENSE 파일을 확인하세요.
